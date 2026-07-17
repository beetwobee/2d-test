(() => {
  'use strict';
  const NS = 'http://www.w3.org/2000/svg';
  const $ = (s, root = document) => root.querySelector(s);
  const $$ = (s, root = document) => [...root.querySelectorAll(s)];
  const svg = (tag, attrs = {}) => { const el = document.createElementNS(NS, tag); Object.entries(attrs).forEach(([k,v]) => el.setAttribute(k, v)); return el; };
  const deep = value => JSON.parse(JSON.stringify(value));
  const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
  const uid = () => `m${Date.now().toString(36)}${Math.random().toString(36).slice(2,7)}`;
  const cm = n => Math.round(n) / 10;
  const px = n => Number(n) * 10;
  let BOARD_W = 1000, BOARD_H = 720, BOARD_CX = 500, BOARD_CY = 360;

  const state = {
    items: [], selected: [], guides: [], grid: true, perspective: false, guidesVisible: true, snap: true, orientation: 'landscape', landscapeLeft: null,
    view: { zoom: 1, x: 0, y: 0, rotation: 0 }, history: [], future: [], opMode: null, opPicks: [], preview: null, selectedGuide: null,
  };
  let orderSeed = 0;
  let gesture = null;
  let wheelSizingActive = false;
  let wheelSizingTimer = null;
  const touchPoints = new Map();
  let tapCandidate = null;
  const tapSequence = { count:0, itemId:null, x:0, y:0, time:0, timer:null, startLayer:null };
  let selectedShape = 'rect';
  const imageCache = new Map();

  const els = {
    canvas: $('#canvas'), viewport: $('#viewportGroup'), grid: $('#gridLayer'), guides: $('#guideLayer'), materials: $('#materialLayer'),
    preview: $('#previewLayer'), selection: $('#selectionLayer'), list: $('#materialList'), count: $('#materialCount'),
    status: $('#selectionStatus'), coords: $('#coordStatus'), layer: $('#layerReadout'), toast: $('#modeToast'), confirm: $('#booleanConfirm')
  };

  function snapshot() {
    state.history.push(JSON.stringify({items: state.items, guides: state.guides}));
    if (state.history.length > 60) state.history.shift();
    state.future.length = 0;
  }
  function restore(raw) {
    const data = JSON.parse(raw); state.items = data.items; state.guides = data.guides || []; state.selected = []; cancelBoolean(); render();
  }
  function undo() { if (!state.history.length) return; state.future.push(JSON.stringify({items:state.items,guides:state.guides})); restore(state.history.pop()); }
  function redo() { if (!state.future.length) return; state.history.push(JSON.stringify({items:state.items,guides:state.guides})); restore(state.future.pop()); }

  function selectedItems() { return state.selected.map(id => state.items.find(i => i.id === id)).filter(Boolean); }
  function primary() { return selectedItems()[0] || null; }
  function textureFill(item) { return item.texture && item.texture !== 'basic' ? `url(#tex-${item.texture})` : null; }
  function shapeNode(item, attrs = {}) {
    const common = { fill: item.fill || '#d6ff3f', stroke: item.stroke || 'none', 'stroke-width': item.strokeWidth || 0, ...attrs };
    if (item.kind === 'ellipse') return svg('ellipse', {cx:0,cy:0,rx:item.w/2,ry:item.h/2,...common});
    if (item.kind === 'triangle') return svg('polygon', {points:`0,${-item.h/2} ${item.w/2},${item.h/2} ${-item.w/2},${item.h/2}`,...common});
    if (item.kind === 'polygon') {
      const pts = Array.from({length:item.sides || 6},(_,k)=>{const a=-Math.PI/2+k*Math.PI*2/(item.sides||6);return `${Math.cos(a)*item.w/2},${Math.sin(a)*item.h/2}`}).join(' ');
      return svg('polygon',{points:pts,...common});
    }
    if (item.kind === 'line') return svg('line',{x1:-item.w/2,y1:0,x2:item.w/2,y2:0,fill:'none',stroke:item.fill,'stroke-width':Math.max(item.h,2),'stroke-linecap':'round',...attrs});
    if (item.kind === 'curve') {
      const bend = -(item.curve || .35) * item.h * 1.5;
      return svg('path',{d:`M ${-item.w/2} 0 Q 0 ${bend} ${item.w/2} 0`,fill:'none',stroke:item.fill,'stroke-width':Math.max(item.strokeWidth || item.h,2),'stroke-linecap':'round',...attrs});
    }
    return svg('rect',{x:-item.w/2,y:-item.h/2,width:item.w,height:item.h,rx:Math.min(item.radius || 0,item.w/2,item.h/2),...common});
  }

  function itemLocalBounds(item) {
    if (item.kind === 'line') {
      const halfStroke = Math.max(item.h || 0, 2) / 2;
      return { x:-item.w/2-halfStroke, y:-halfStroke, w:item.w+halfStroke*2, h:halfStroke*2 };
    }
    if (item.kind === 'curve') {
      const halfStroke = Math.max(item.strokeWidth || item.h || 0, 2) / 2;
      const bend = -(item.curve || .35) * item.h * .75;
      const top = Math.min(0, bend) - halfStroke, bottom = Math.max(0, bend) + halfStroke;
      return { x:-item.w/2-halfStroke, y:top, w:item.w+halfStroke*2, h:bottom-top };
    }
    const halfStroke = Math.max(item.strokeWidth || 0, 0) / 2;
    return { x:-item.w/2-halfStroke, y:-item.h/2-halfStroke, w:item.w+halfStroke*2, h:item.h+halfStroke*2 };
  }
  function itemWorldBounds(item) {
    const b=itemLocalBounds(item),a=(item.rotation||0)*Math.PI/180,c=Math.cos(a),s=Math.sin(a);
    const points=[[b.x,b.y],[b.x+b.w,b.y],[b.x+b.w,b.y+b.h],[b.x,b.y+b.h]].map(([x,y])=>({x:item.x+x*c-y*s,y:item.y+x*s+y*c}));
    return { left:Math.min(...points.map(p=>p.x)), right:Math.max(...points.map(p=>p.x)), top:Math.min(...points.map(p=>p.y)), bottom:Math.max(...points.map(p=>p.y)) };
  }
  function itemsOverlap(a,b) {
    const x=itemWorldBounds(a),y=itemWorldBounds(b);
    return x.left<y.right&&x.right>y.left&&x.top<y.bottom&&x.bottom>y.top;
  }
  function moveLayerSmart(item,direction) {
    const step=direction==='front'?1:-1;
    const candidates=state.items.filter(other=>other.id!==item.id&&other.visible!==false&&itemsOverlap(item,other)&&(
      direction==='front'?other.layer>item.layer:other.layer<item.layer
    ));
    if (!candidates.length) { item.layer+=step; return; }
    const nearest=candidates.reduce((best,other)=>Math.abs(other.layer-item.layer)<Math.abs(best.layer-item.layer)?other:best);
    item.layer=nearest.layer+step;
  }

  function makeMaterialNode(item, options={}) {
    const g = svg('g',{class:`material${item.locked?' locked':''}${state.selected.includes(item.id)?' selected':''}`,transform:`translate(${item.x} ${item.y}) rotate(${item.rotation||0})`,opacity:item.opacity ?? 1,'data-id':item.id});
    if (item.shadow) g.setAttribute('filter','url(#softShadow)');
    if (item.kind === 'image') {
      const im = svg('image',{href:item.data,x:-item.w/2,y:-item.h/2,width:item.w,height:item.h,preserveAspectRatio:'none'}); g.append(im);
      if (item.texture && item.texture !== 'basic') {
        const ov=svg('rect',{x:-item.w/2,y:-item.h/2,width:item.w,height:item.h,fill:textureFill(item),opacity:(item.textureStrength??.45),style:'mix-blend-mode:overlay;pointer-events:none'}); g.append(ov);
      }
    } else {
      g.append(shapeNode(item));
      if (item.texture && item.texture !== 'basic') g.append(shapeNode(item,{fill:textureFill(item),stroke:'none',opacity:(item.textureStrength??.45),style:'mix-blend-mode:overlay;pointer-events:none'}));
    }
    if (!options.passive && !item.locked) g.addEventListener('pointerdown', e => materialPointerDown(e,item));
    return g;
  }

  function renderGuides() {
    els.guides.replaceChildren();
    if (!state.guidesVisible) { updateGuideEditor(); renderGuideList(); return; }
    state.guides.forEach(g => {
      if(g.visible===false)return;
      const group=svg('g',{'data-guide-id':g.id});
      if(g.type==='circle'){
        const visible=svg('circle',{class:`guide${state.selectedGuide===g.id?' selected':''}`,cx:g.x,cy:g.y,r:g.radius||100,fill:'none'}),hit=svg('circle',{class:'guide-hit',cx:g.x,cy:g.y,r:g.radius||100});
        if(!g.locked)hit.addEventListener('pointerdown',e=>guidePointerDown(e,g,'resize'));else hit.style.pointerEvents='none';group.append(visible,hit);
      }else{
        const rad=(g.angle||0)*Math.PI/180,r=1200,attrs={x1:g.x-Math.cos(rad)*r,y1:g.y-Math.sin(rad)*r,x2:g.x+Math.cos(rad)*r,y2:g.y+Math.sin(rad)*r};
        const visible=svg('line',{class:`guide${state.selectedGuide===g.id?' selected':''}`,...attrs}),hit=svg('line',{class:'guide-hit',...attrs});
        if(!g.locked)hit.addEventListener('pointerdown',e=>guidePointerDown(e,g,'rotate'));else hit.style.pointerEvents='none';group.append(visible,hit);
      }
      const centerHit=svg('circle',{class:'guide-center-hit',cx:g.x,cy:g.y,r:16}),center=svg('circle',{class:'guide-center',cx:g.x,cy:g.y,r:4});if(!g.locked){centerHit.addEventListener('pointerdown',e=>guidePointerDown(e,g,'move'));center.addEventListener('pointerdown',e=>guidePointerDown(e,g,'move'))}else{centerHit.style.pointerEvents='none';center.style.pointerEvents='none'}group.append(centerHit,center);
      els.guides.append(group);
    });
    updateGuideEditor();renderGuideList();
  }

  function guidePointerDown(e,g,action='move'){e.stopPropagation();state.selectedGuide=g.id;if(g.locked){renderGuides();return}const p=pointFromEvent(e);snapshot();gesture={type:'guide',action,guide:g,start:p,base:{x:g.x,y:g.y,angle:g.angle||0,radius:g.radius||100}};els.canvas.setPointerCapture(e.pointerId);renderGuides()}
  function updateGuideEditor(){
    const g=state.guides.find(x=>x.id===state.selectedGuide),box=$('#guideEditor');box.hidden=!g;if(!g)return;
    const names={line:'직선 가이드',vertical:'직선 가이드',horizontal:'직선 가이드',radial:'직선 가이드',circle:'원 가이드'};$('#guideEditorTitle').textContent=names[g.type]||'가이드 설정';
    $('#guideRotationRow').hidden=g.type==='circle';$('#circleGuideControls').hidden=g.type!=='circle';$('#guideRadius').value=cm(g.radius||100);
  }
  function renderGuideList(){
    const list=$('#guideList');list.replaceChildren();
    state.guides.forEach((g,index)=>{const row=document.createElement('div');row.className=`material-row guide-item${state.selectedGuide===g.id?' active':''}`;const name=g.type==='circle'?'원':'직선',eye=g.visible===false?'<svg viewBox="0 0 24 24"><path d="M17.94 17.94A10.94 10.94 0 0 1 12 20C5 20 1 12 1 12a21.8 21.8 0 0 1 5.06-5.94"/><path d="M9.9 4.24A10.94 10.94 0 0 1 12 4c7 0 11 8 11 8a21.77 21.77 0 0 1-2.16 3.19"/><path d="M14.12 14.12A3 3 0 1 1 9.88 9.88M1 1l22 22"/></svg>':'<svg viewBox="0 0 24 24"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8S1 12 1 12Z"/><circle cx="12" cy="12" r="3"/></svg>',lock=g.locked?'<svg viewBox="0 0 24 24"><rect x="5" y="10" width="14" height="10" rx="2"/><path d="M8 10V7a4 4 0 0 1 8 0v3"/></svg>':'<svg viewBox="0 0 24 24"><rect x="5" y="10" width="14" height="10" rx="2"/><path d="M8 10V7a4 4 0 0 1 7.5-2"/></svg>';
      const typeIcon=g.type==='circle'?'<svg class="guide-type-icon" viewBox="0 0 24 24"><circle cx="12" cy="12" r="8"/></svg>':'<svg class="guide-type-icon" viewBox="0 0 24 24"><path d="M4 20 20 4"/></svg>';
      row.innerHTML=`<span class="info"><b>${typeIcon}${name} ${index+1}</b></span><span class="model-actions guide-actions"><button class="mini-btn" data-act="dup" title="같은 가이드 추가"><svg viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></svg></button><button class="mini-btn ${g.visible===false?'off':''}" data-act="vis" title="표시·숨기기">${eye}</button><button class="mini-btn ${g.locked?'locked':''}" data-act="lock" title="잠금">${lock}</button><button class="mini-btn danger" data-act="del" title="삭제"><svg viewBox="0 0 24 24"><path d="M3 6h18M8 6V4h8v2M19 6l-1 14H6L5 6M10 11v6M14 11v6"/></svg></button></span>`;
      row.onclick=e=>{if(e.target.closest('button'))return;if(!g.locked){state.selectedGuide=g.id;renderGuides()}};$('[data-act="dup"]',row).onclick=()=>{snapshot();const copy={...deep(g),id:uid(),locked:false};state.guides.push(copy);state.selectedGuide=copy.id;renderGuides()};$('[data-act="vis"]',row).onclick=()=>{snapshot();g.visible=g.visible===false;renderGuides()};$('[data-act="lock"]',row).onclick=()=>{snapshot();g.locked=!g.locked;if(g.locked&&state.selectedGuide===g.id)state.selectedGuide=null;renderGuides()};$('[data-act="del"]',row).onclick=()=>{snapshot();state.guides=state.guides.filter(x=>x.id!==g.id);if(state.selectedGuide===g.id)state.selectedGuide=null;renderGuides()};list.append(row)});
  }

  function renderMaterials() {
    els.materials.replaceChildren();
    [...state.items].filter(i=>i.visible!==false).sort((a,b)=>(a.layer-b.layer)||(a.order-b.order)).forEach(i=>els.materials.append(makeMaterialNode(i)));
  }
  function renderPreview() {
    els.preview.replaceChildren();
    if (!state.preview) return;
    state.preview.results.forEach(r=>{
      const im=svg('image',{class:'preview-item',href:r.data,x:r.x-r.w/2,y:r.y-r.h/2,width:r.w,height:r.h});
      els.preview.append(im,svg('rect',{class:'preview-outline',x:r.x-r.w/2,y:r.y-r.h/2,width:r.w,height:r.h}));
    });
  }
  function renderSelection() {
    els.selection.replaceChildren();
    selectedItems().filter(item=>item.visible!==false).forEach(item=>{
      const g=svg('g',{transform:`translate(${item.x} ${item.y}) rotate(${item.rotation||0})`});
      g.append(svg('rect',{class:'selection-box',x:-item.w/2,y:-item.h/2,width:item.w,height:item.h}));
      if (!item.locked && state.selected.length===1) {
        const handle=svg('g',{class:'handle-group',transform:`translate(${item.w/2} ${item.h/2})`});
        handle.append(svg('rect',{class:'handle-bg',x:-10,y:-10,width:20,height:20,rx:5}),svg('path',{class:'handle-icon',d:'M-5 5 5-5 M1-5H5V-1 M-5 1V5H-1'}));
        const line=svg('line',{class:'rotate-line',x1:0,y1:-item.h/2,x2:0,y2:-item.h/2-20});
        const rotate=svg('g',{class:'rotate-group',transform:`translate(0 ${-item.h/2-25})`});
        rotate.append(svg('circle',{class:'handle-bg',cx:0,cy:0,r:11}),svg('path',{class:'handle-icon',d:'M -6.3 0 A 6.3 6.3 0 1 0 -4.45 -4.45 L -6.3 -2.8 M -6.3 -6.3 V -2.8 H -2.8'}));
        handle.addEventListener('pointerdown',e=>handlePointerDown(e,item,'resize'));
        rotate.addEventListener('pointerdown',e=>handlePointerDown(e,item,'rotate'));
        g.append(line,handle,rotate);
      }
      if(state.perspective){const b=itemLocalBounds(item);g.append(svg('rect',{class:'perspective-outline',x:b.x,y:b.y,width:b.w,height:b.h}));for(let k=1;k<4;k++){g.append(svg('line',{class:'perspective-line',x1:b.x+k*b.w/4,y1:b.y,x2:b.x+k*b.w/4,y2:b.y+b.h}));g.append(svg('line',{class:'perspective-line',x1:b.x,y1:b.y+k*b.h/4,x2:b.x+b.w,y2:b.y+k*b.h/4}));}}
      els.selection.append(g);
    });
  }
  function renderList() {
    els.list.replaceChildren();
    if(!state.items.length) els.list.innerHTML='<div class="empty-state">소재를 추가하거나 도형을 제작하세요.</div>';
    [...state.items].sort((a,b)=>(b.layer-a.layer)||(b.order-a.order)).forEach(item=>{
      const row=document.createElement('div'); row.className=`material-row${state.selected.includes(item.id)?' active':''}`;
      const typeLabel=item.kind==='image'?'PNG':'SVG';
      const lockIcon=item.locked?'<svg viewBox="0 0 24 24"><rect x="5" y="10" width="14" height="10" rx="2"/><path d="M8 10V7a4 4 0 0 1 8 0v3"/></svg>':'<svg viewBox="0 0 24 24"><rect x="5" y="10" width="14" height="10" rx="2"/><path d="M8 10V7a4 4 0 0 1 7.5-2"/></svg>',eyeIcon=item.visible===false?'<svg viewBox="0 0 24 24"><path d="M17.94 17.94A10.94 10.94 0 0 1 12 20C5 20 1 12 1 12a21.8 21.8 0 0 1 5.06-5.94"/><path d="M9.9 4.24A10.94 10.94 0 0 1 12 4c7 0 11 8 11 8a21.77 21.77 0 0 1-2.16 3.19"/><path d="M14.12 14.12A3 3 0 1 1 9.88 9.88M1 1l22 22"/></svg>':'<svg viewBox="0 0 24 24"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8S1 12 1 12Z"/><circle cx="12" cy="12" r="3"/></svg>';
      row.innerHTML=`<span class="info"><b><i class="ext">${typeLabel}</i>${escapeHtml(item.name)}</b><small>LAYER ${item.layer}</small></span><span class="model-actions"><button class="mini-btn duplicate" title="같은 소재 추가"><svg viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></svg></button><button class="mini-btn visibility ${item.visible===false?'off':''}" title="표시·숨기기">${eyeIcon}</button><button class="mini-btn lock ${item.locked?'locked':''}" title="잠금">${lockIcon}</button><button class="mini-btn delete" title="삭제"><svg viewBox="0 0 24 24"><path d="M3 6h18M8 6V4h8v2M19 6l-1 14H6L5 6M10 11v6M14 11v6"/></svg></button></span>`;
      row.addEventListener('click',e=>{if(e.target.closest('button')||item.locked)return;selectItem(item.id,e.ctrlKey||e.metaKey||e.shiftKey)});
      $('.duplicate',row).onclick=()=>{snapshot();const copy={...deep(item),id:uid(),name:item.name+' 복사',x:item.x+20,y:item.y+20,order:++orderSeed,locked:false};state.items.push(copy);state.selected=[copy.id];render()};
      $('.visibility',row).onclick=()=>{snapshot();item.visible=item.visible===false;if(item.visible===false)state.selected=state.selected.filter(id=>id!==item.id);render()};
      $('.lock',row).onclick=()=>{snapshot();item.locked=!item.locked;if(item.locked)state.selected=state.selected.filter(id=>id!==item.id);render()};
      $('.delete',row).onclick=()=>{snapshot();state.items=state.items.filter(i=>i.id!==item.id);state.selected=state.selected.filter(id=>id!==item.id);render()};
      els.list.append(row);
    });
    els.count.textContent=`${state.items.length} ITEMS`;$('#materialCountHeader').textContent=state.items.length;
  }
  function escapeHtml(s){return String(s).replace(/[&<>'"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;',"'":'&#39;','"':'&quot;'}[c]));}

  function updateInspector() {
    const item=primary(), fields=['posX','posY','itemWidth','itemHeight','itemRotation'];
    fields.forEach(id=>$('#'+id).disabled=!item);
    if(item){$('#posX').value=cm(item.x);$('#posY').value=cm(item.y);$('#itemWidth').value=cm(item.w);$('#itemHeight').value=cm(item.h);$('#itemRotation').value=Math.round(item.rotation||0);$('#ratioToggle').checked=item.keepRatio!==false;$('#shadowToggle').checked=!!item.shadow;$('#materialOpacity').value=Math.round((item.opacity??1)*100);$('#textureStrength').value=Math.round((item.textureStrength??.45)*100);$('#textureValue').value=$('#textureStrength').value+'%';$('#opacityValue').value=$('#materialOpacity').value+'%';els.layer.textContent=`LAYER ${item.layer}`;els.status.textContent=state.selected.length>1?`${state.selected.length}개 소재 선택`:item.name;$$('#textureGrid button').forEach(b=>b.classList.toggle('active',b.dataset.texture===(item.texture||'basic')))}
    else{els.layer.textContent='LAYER —';els.status.textContent='선택 없음'}
  }
  function renderGridGeometry() {
    const minorX=[1,3,5].map(n=>BOARD_W*n/6),minorY=[1,3,5].map(n=>BOARD_H*n/6);
    const majorX=[1,2].map(n=>BOARD_W*n/3),majorY=[1,2].map(n=>BOARD_H*n/3);
    $('.grid-lines.minor path').setAttribute('d',[...minorX.map(x=>`M${x} 0V${BOARD_H}`),...minorY.map(y=>`M0 ${y}H${BOARD_W}`)].join(' '));
    $('.grid-lines.major path').setAttribute('d',[...majorX.map(x=>`M${x} 0V${BOARD_H}`),...majorY.map(y=>`M0 ${y}H${BOARD_W}`)].join(' '));
  }
  function setOrientation(orientation,shouldRender=true) {
    const portrait=orientation==='portrait';state.orientation=portrait?'portrait':'landscape';
    BOARD_W=portrait?720:1000;BOARD_H=portrait?1000:720;BOARD_CX=BOARD_W/2;BOARD_CY=BOARD_H/2;
    els.canvas.setAttribute('viewBox',`0 0 ${BOARD_W} ${BOARD_H}`);els.canvas.classList.toggle('portrait',portrait);
    $('.board').setAttribute('width',BOARD_W);$('.board').setAttribute('height',BOARD_H);
    $('#boardClipRect').setAttribute('width',BOARD_W);$('#boardClipRect').setAttribute('height',BOARD_H);
    const button=$('#orientationToggle'),icon=$('#orientationIcon');$('span',button).textContent=portrait?'세로':'가로';
    icon.setAttribute('x',portrait?6:3);icon.setAttribute('y',portrait?3:6);icon.setAttribute('width',portrait?12:18);icon.setAttribute('height',portrait?18:12);
    button.title=portrait?'세로 화면 (클릭하여 가로로 전환)':'가로 화면 (클릭하여 세로로 전환)';
    renderGridGeometry();positionCanvasForOrientation();if(shouldRender)render();
  }
  function positionCanvasForOrientation() {
    const wrap=$('#canvasWrap');
    if(state.orientation!=='portrait'){
      wrap.classList.remove('portrait-layout');wrap.style.removeProperty('--portrait-left');
      ['position','top','bottom','left','right','margin-left','margin-right','transform'].forEach(name=>els.canvas.style.removeProperty(name));
      wrap.style.justifyContent='center';
      requestAnimationFrame(()=>{if(state.orientation==='landscape'){const wr=wrap.getBoundingClientRect(),cr=els.canvas.getBoundingClientRect();state.landscapeLeft=cr.left-wr.left}});return;
    }
    wrap.classList.add('portrait-layout');wrap.style.justifyContent='center';
    ['position','top','bottom','left','right','margin-left','margin-right'].forEach(name=>els.canvas.style.removeProperty(name));els.canvas.style.transform='none';
    requestAnimationFrame(()=>requestAnimationFrame(()=>{
      if(state.orientation!=='portrait')return;
      const wr=wrap.getBoundingClientRect(),cr=els.canvas.getBoundingClientRect(),panel=$('#sidePanel').getBoundingClientRect();
      const fallback=Math.max(0,(wr.width-Math.min(wr.width,wr.height*(1000/720)))/2);
      const landscapeLeft=Number.isFinite(state.landscapeLeft)?state.landscapeLeft:fallback;
      const panelLimit=Math.max(0,panel.left-wr.left-cr.width),targetLeft=Math.min(landscapeLeft,panelLimit);
      const shift=targetLeft-(cr.left-wr.left);wrap.style.setProperty('--portrait-left',`${targetLeft}px`);els.canvas.style.transform=`translateX(${shift}px)`;
    }));
  }
  function applyOrientationToContent() {
    const portrait=state.orientation==='portrait',scale=1000/720;
    const transform=portrait?`translate(${BOARD_CX} ${BOARD_CY}) scale(${scale}) translate(-500 -360)`:'';
    [els.materials,els.preview,els.guides,els.selection].forEach(layer=>layer.setAttribute('transform',transform));
  }
  function editingBounds() {
    if(state.orientation!=='portrait')return{l:0,r:1000,t:0,b:720,cx:500,cy:360};
    const scale=1000/720,halfW=BOARD_W/(2*scale),halfH=BOARD_H/(2*scale);
    return{l:500-halfW,r:500+halfW,t:360-halfH,b:360+halfH,cx:500,cy:360};
  }
  function applyView() {
    const v=state.view; els.viewport.setAttribute('transform',`translate(${BOARD_CX+v.x} ${BOARD_CY+v.y}) rotate(${v.rotation}) scale(${v.zoom}) translate(${-BOARD_CX} ${-BOARD_CY})`);
    applyOrientationToContent();
    $('#zoomReadout').textContent=$('#viewZoomValue').textContent=`${Math.round(v.zoom*100)}%`;$('#viewZoom').value=Math.round(v.zoom*100);$('#viewRotationValue').textContent=`${v.rotation}°`;
  }
  function render(){els.grid.style.display=state.grid?'':'none';$('#gridToggle').classList.toggle('active',state.grid);$('#perspectiveToggle').classList.toggle('active',state.perspective);renderGuides();renderMaterials();renderPreview();renderSelection();renderList();updateInspector();applyView();}

  function pointFromEvent(e) { const pt=els.canvas.createSVGPoint();pt.x=e.clientX;pt.y=e.clientY;return pt.matrixTransform(els.materials.getScreenCTM().inverse()); }
  function selectItem(id,multi=false){
    if(state.opMode){ if(!state.opPicks.includes(id))state.opPicks.push(id);state.selected=[...state.opPicks];showToast(`${opName(state.opMode)} · ${state.opPicks.length}/2 소재 선택`);render();if(state.opPicks.length===2)createBooleanPreview();return; }
    if(state.perspective&&!multi&&!state.selected.includes(id))state.perspective=false;
    state.selected=multi?(state.selected.includes(id)?state.selected.filter(x=>x!==id):[...state.selected,id]):[id];render();
  }
  function materialPointerDown(e,item){
    e.stopPropagation();if(state.opMode){selectItem(item.id);return}if(!state.selected.includes(item.id))selectItem(item.id,e.ctrlKey||e.metaKey||e.shiftKey);if(item.locked)return;const p=pointFromEvent(e);els.canvas.setPointerCapture(e.pointerId);
    tapCandidate={pointerId:e.pointerId,itemId:item.id,x:e.clientX,y:e.clientY,moved:false};
    if(e.pointerType==='touch'){touchPoints.set(e.pointerId,p);if(touchPoints.size>=2){tapCandidate=null;const pts=[...touchPoints.values()],target=primary();snapshot();gesture={type:'pinch',item:target,startDist:Math.hypot(pts[0].x-pts[1].x,pts[0].y-pts[1].y),baseW:target.w,baseH:target.h};return}}
    snapshot();gesture={type:'move',start:p,base:selectedItems().map(i=>({id:i.id,x:i.x,y:i.y}))};
  }
  function handlePointerDown(e,item,type){e.stopPropagation();const p=pointFromEvent(e);snapshot();gesture={type,item,start:p,base:deep(item)};els.canvas.setPointerCapture(e.pointerId)}
  function snappedPoint(x,y){
    if(!state.snap||!state.guidesVisible)return{x,y};let sx=x,sy=y;
    state.guides.forEach(g=>{
      if(g.type!=='circle'){
        const dx=x-g.x,dy=y-g.y;
        const rad=(g.angle||0)*Math.PI/180,ux=Math.cos(rad),uy=Math.sin(rad),along=dx*ux+dy*uy,perp=Math.abs(dx*uy-dy*ux);if(perp<10){sx=g.x+ux*along;sy=g.y+uy*along}
      }
      if(g.type==='circle'){
        const dx=x-g.x,dy=y-g.y,d=Math.hypot(dx,dy);
        if(d<12){sx=g.x;sy=g.y;return}
        const r=g.radius||100;if(Math.abs(d-r)<10){sx=g.x+dx/d*r;sy=g.y+dy/d*r}
      }
    });return{x:sx,y:sy}
  }
  els.canvas.addEventListener('pointermove',e=>{
    const p=pointFromEvent(e);els.coords.textContent=`X ${cm(p.x).toFixed(1)} · Y ${cm(p.y).toFixed(1)} CM`;
    if(tapCandidate?.pointerId===e.pointerId&&Math.hypot(e.clientX-tapCandidate.x,e.clientY-tapCandidate.y)>10)tapCandidate.moved=true;
    if(e.pointerType==='touch'&&touchPoints.has(e.pointerId))touchPoints.set(e.pointerId,p);
    if(!gesture)return;
    if(gesture.type==='pinch'){const pts=[...touchPoints.values()];if(pts.length>=2){const d=Math.hypot(pts[0].x-pts[1].x,pts[0].y-pts[1].y),scale=clamp(d/Math.max(gesture.startDist,1),.08,20);gesture.item.w=gesture.baseW*scale;gesture.item.h=gesture.baseH*scale;renderMaterials();renderSelection();updateInspector();renderList()}return}
    if(gesture.type==='guide'){const g=gesture.guide,dx=p.x-gesture.start.x,dy=p.y-gesture.start.y;if(gesture.action==='move'){const bounds=editingBounds();let nx=clamp(gesture.base.x+dx,bounds.l,bounds.r),ny=clamp(gesture.base.y+dy,bounds.t,bounds.b);for(const other of state.guides){if(other.id!==g.id&&Math.hypot(nx-other.x,ny-other.y)<22){nx=other.x;ny=other.y;break}}g.x=nx;g.y=ny}else if(gesture.action==='rotate'){g.angle=(Math.atan2(p.y-g.y,p.x-g.x)*180/Math.PI+360)%360}else if(gesture.action==='resize'){g.radius=clamp(Math.hypot(p.x-g.x,p.y-g.y),20,600)}renderGuides();return}
    if(gesture.type==='move'){const dx=p.x-gesture.start.x,dy=p.y-gesture.start.y,bounds=editingBounds();gesture.base.forEach(b=>{const i=state.items.find(x=>x.id===b.id);if(i&&!i.locked){const s=snappedPoint(b.x+dx,b.y+dy);i.x=clamp(s.x,bounds.l,bounds.r);i.y=clamp(s.y,bounds.t,bounds.b)}})}
    if(gesture.type==='resize'){const i=gesture.item,b=gesture.base;const local=toLocal(p,b);i.w=Math.max(5,Math.abs(local.x)*2);i.h=i.keepRatio===false?Math.max(5,Math.abs(local.y)*2):i.w*(b.h/b.w)}
    if(gesture.type==='rotate'){const i=gesture.item;let a=Math.atan2(p.y-i.y,p.x-i.x)*180/Math.PI+90;if(e.shiftKey)a=Math.round(a/15)*15;i.rotation=Math.round(a*10)/10}
    renderMaterials();renderSelection();updateInspector();renderList();
  });
  function registerMaterialTap(tap){
    const now=Date.now(),same=tapSequence.itemId===tap.itemId&&now-tapSequence.time<=500&&Math.hypot(tap.x-tapSequence.x,tap.y-tapSequence.y)<24;
    if(!same){clearTimeout(tapSequence.timer);tapSequence.count=0;tapSequence.itemId=tap.itemId;tapSequence.x=tap.x;tapSequence.y=tap.y;tapSequence.startLayer=null}
    tapSequence.count++;tapSequence.time=now;clearTimeout(tapSequence.timer);
    const item=state.items.find(i=>i.id===tap.itemId);
    if(tapSequence.count===1&&item)tapSequence.startLayer=item.layer;
    if(tapSequence.count===2&&item&&!item.locked){moveLayerSmart(item,'back');state.selected=[item.id];render()}
    if(tapSequence.count>=3){if(item&&!item.locked){item.layer=tapSequence.startLayer;moveLayerSmart(item,'front');state.selected=[item.id];render()}tapSequence.count=0;tapSequence.itemId=null;tapSequence.startLayer=null;return}
    tapSequence.timer=setTimeout(()=>{tapSequence.count=0;tapSequence.itemId=null;tapSequence.startLayer=null},500);
  }
  els.canvas.addEventListener('pointerup',e=>{touchPoints.delete(e.pointerId);if(tapCandidate?.pointerId===e.pointerId&&!tapCandidate.moved&&gesture?.type!=='pinch')registerMaterialTap(tapCandidate);tapCandidate=null;gesture=null});
  els.canvas.addEventListener('pointercancel',e=>{touchPoints.delete(e.pointerId);tapCandidate=null;gesture=null});
  els.canvas.addEventListener('pointerdown',e=>{if(e.target===els.canvas||e.target.classList.contains('board')||e.target.classList.contains('grid-minor')||e.target.classList.contains('grid-major')){if(!state.opMode){state.perspective=false;state.selected=[];state.selectedGuide=null;render()}}});
  function toLocal(p,item){const a=-(item.rotation||0)*Math.PI/180,dx=p.x-item.x,dy=p.y-item.y;return{x:dx*Math.cos(a)-dy*Math.sin(a),y:dx*Math.sin(a)+dy*Math.cos(a)}}

  function addItem(data){snapshot();const bounds=editingBounds(),item={id:uid(),name:'새 소재',x:bounds.cx,y:bounds.cy,w:240,h:160,rotation:0,layer:0,order:++orderSeed,fill:'#7c5cff',stroke:'#18202c',strokeWidth:0,opacity:1,texture:'basic',textureStrength:.45,shadow:false,locked:false,visible:true,keepRatio:true,...data};state.items.push(item);state.selected=[item.id];render();return item}
  function createShape(){const kind=selectedShape,w=px($('#shapeWidth').value),h=px($('#shapeHeight').value);addItem({kind,name:$('#shapeName').value||'새 도형',w,h:kind==='line'||kind==='curve'?Math.max(px($('#strokeWidth').value||.8),8):h,radius:px($('#shapeRadius').value),sides:+$('#shapeSides').value,curve:+$('#curveAmount').value/100,fill:$('#shapeColor').value,stroke:$('#strokeColor').value,strokeWidth:px($('#strokeWidth').value),opacity:+$('#shapeOpacity').value/100});}

  async function trimImage(file){
    const data=await fileToData(file),img=await loadImage(data),c=document.createElement('canvas');c.width=img.naturalWidth;c.height=img.naturalHeight;const ctx=c.getContext('2d');ctx.drawImage(img,0,0);let box={l:0,t:0,r:c.width-1,b:c.height-1};
    if(file.type==='image/png'){const d=ctx.getImageData(0,0,c.width,c.height).data;let l=c.width,t=c.height,r=-1,b=-1;for(let y=0;y<c.height;y++)for(let x=0;x<c.width;x++)if(d[(y*c.width+x)*4+3]>2){l=Math.min(l,x);t=Math.min(t,y);r=Math.max(r,x);b=Math.max(b,y)}if(r>=l)box={l,t,r,b};}
    const out=document.createElement('canvas');out.width=box.r-box.l+1;out.height=box.b-box.t+1;out.getContext('2d').drawImage(c,box.l,box.t,out.width,out.height,0,0,out.width,out.height);return{data:out.toDataURL('image/png'),ratio:out.width/out.height};
  }
  const fileToData=file=>new Promise((res,rej)=>{const r=new FileReader();r.onload=()=>res(r.result);r.onerror=rej;r.readAsDataURL(file)});
  const loadImage=src=>imageCache.has(src)?imageCache.get(src):new Promise((res,rej)=>{const i=new Image();i.onload=()=>res(i);i.onerror=rej;i.src=src}).then(i=>(imageCache.set(src,Promise.resolve(i)),i));

  function updateSelected(mutator){const arr=selectedItems();if(!arr.length)return;snapshot();arr.forEach(mutator);render()}
  function rotateSelected(deg){updateSelected(i=>i.rotation=((i.rotation||0)+deg+360)%360)}
  function alignItems(type){const arr=selectedItems();if(!arr.length)return;snapshot();const ref=arr.length===1?editingBounds():{l:Math.min(...arr.map(i=>i.x-i.w/2)),r:Math.max(...arr.map(i=>i.x+i.w/2)),t:Math.min(...arr.map(i=>i.y-i.h/2)),b:Math.max(...arr.map(i=>i.y+i.h/2))};ref.cx??=(ref.l+ref.r)/2;ref.cy??=(ref.t+ref.b)/2;arr.forEach(i=>{if(i.locked)return;if(type==='left')i.x=ref.l+i.w/2;if(type==='right')i.x=ref.r-i.w/2;if(type==='centerX')i.x=ref.cx;if(type==='top')i.y=ref.t+i.h/2;if(type==='bottom')i.y=ref.b-i.h/2;if(type==='centerY')i.y=ref.cy});render()}

  function opName(op){return({union:'합치기',intersect:'중첩',cut:'자르기'})[op]}
  function beginBoolean(op){state.opMode=op;state.opPicks=[];state.selected=[];state.preview=null;els.confirm.hidden=true;showToast(`${opName(op)} · 첫 번째 소재를 선택하세요`);render()}
  function showToast(text){els.toast.textContent=text;els.toast.hidden=false}
  function cancelBoolean(){state.opMode=null;state.opPicks=[];state.preview=null;els.confirm.hidden=true;els.toast.hidden=true;renderPreview()}
  async function createBooleanPreview(){
    const [a,b]=state.opPicks.map(id=>state.items.find(i=>i.id===id)); if(!a||!b)return;
    showToast('미리보기를 계산하고 있습니다…');
    const l=Math.max(0,Math.min(a.x-a.w/2,b.x-b.w/2)-20),t=Math.max(0,Math.min(a.y-a.h/2,b.y-b.h/2)-20),r=Math.min(BOARD_W,Math.max(a.x+a.w/2,b.x+b.w/2)+20),bt=Math.min(BOARD_H,Math.max(a.y+a.h/2,b.y+b.h/2)+20),w=Math.max(1,Math.ceil(r-l)),h=Math.max(1,Math.ceil(bt-t));
    const ca=document.createElement('canvas'),cb=document.createElement('canvas');ca.width=cb.width=w;ca.height=cb.height=h;await drawCanvasItem(ca.getContext('2d'),a,l,t);await drawCanvasItem(cb.getContext('2d'),b,l,t);
    const result=[];
    const compose=(mode,name)=>{const c=document.createElement('canvas');c.width=w;c.height=h;const x=c.getContext('2d');x.drawImage(ca,0,0);x.globalCompositeOperation=mode;x.drawImage(cb,0,0);result.push({data:c.toDataURL(),x:l+w/2,y:t+h/2,w,h,name})};
    if(state.opMode==='union')compose('source-over','합친 소재');
    if(state.opMode==='intersect')compose('source-in','중첩 소재');
    if(state.opMode==='cut'){compose('destination-out','잘라낸 원본');const c=document.createElement('canvas');c.width=w;c.height=h;const x=c.getContext('2d');x.drawImage(ca,0,0);x.globalCompositeOperation='source-in';x.drawImage(cb,0,0);result.push({data:c.toDataURL(),x:l+w/2,y:t+h/2,w,h,name:'분리된 조각'});}
    state.preview={op:state.opMode,results:result};els.toast.hidden=true;$('#booleanTitle').textContent=`${opName(state.opMode)} 결과 미리보기`;els.confirm.hidden=false;renderPreview();
  }
  async function drawCanvasItem(ctx,item,left,top){ctx.save();ctx.translate(item.x-left,item.y-top);ctx.rotate((item.rotation||0)*Math.PI/180);ctx.globalAlpha=item.opacity??1;if(item.kind==='image'){const im=await loadImage(item.data);ctx.drawImage(im,-item.w/2,-item.h/2,item.w,item.h)}else{ctx.fillStyle=item.fill;ctx.strokeStyle=item.stroke||'transparent';ctx.lineWidth=item.strokeWidth||0;ctx.beginPath();if(item.kind==='ellipse')ctx.ellipse(0,0,item.w/2,item.h/2,0,0,Math.PI*2);else if(item.kind==='triangle'){ctx.moveTo(0,-item.h/2);ctx.lineTo(item.w/2,item.h/2);ctx.lineTo(-item.w/2,item.h/2);ctx.closePath()}else if(item.kind==='polygon'){for(let k=0;k<(item.sides||6);k++){const a=-Math.PI/2+k*Math.PI*2/(item.sides||6),x=Math.cos(a)*item.w/2,y=Math.sin(a)*item.h/2;k?ctx.lineTo(x,y):ctx.moveTo(x,y)}ctx.closePath()}else if(item.kind==='line'||item.kind==='curve'){ctx.lineCap='round';ctx.lineWidth=Math.max(item.h,2);ctx.strokeStyle=item.fill;ctx.moveTo(-item.w/2,0);item.kind==='line'?ctx.lineTo(item.w/2,0):ctx.quadraticCurveTo(0,-(item.curve||.35)*item.h*1.5,item.w/2,0);ctx.stroke();ctx.restore();return}else{ctx.roundRect(-item.w/2,-item.h/2,item.w,item.h,item.radius||0)}ctx.fill();if(item.strokeWidth)ctx.stroke()}ctx.restore()}
  function applyBoolean(){if(!state.preview)return;snapshot();const layer=Math.max(...state.opPicks.map(id=>state.items.find(i=>i.id===id)?.layer||0))+1;const ids=[];state.preview.results.forEach(r=>{const item={id:uid(),kind:'image',name:r.name,data:r.data,x:r.x,y:r.y,w:r.w,h:r.h,rotation:0,layer,order:++orderSeed,opacity:1,texture:'basic',textureStrength:.45,shadow:false,locked:false,keepRatio:true};state.items.push(item);ids.push(item.id)});state.selected=ids;cancelBoolean();render()}

  function download(name,data,type){const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([data],{type}));a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000)}
  function saveProject(){download(`plane-project-${new Date().toISOString().slice(0,10)}.plane`,JSON.stringify({version:2,items:state.items,guides:state.guides,view:state.view,orientation:state.orientation},null,2),'application/json')}
  async function capture(){const clone=els.canvas.cloneNode(true);clone.querySelector('#selectionLayer')?.remove();clone.querySelector('#previewLayer')?.remove();const xml=new XMLSerializer().serializeToString(clone),url='data:image/svg+xml;charset=utf-8,'+encodeURIComponent(xml),img=await loadImage(url),c=document.createElement('canvas');c.width=BOARD_W;c.height=BOARD_H;c.getContext('2d').drawImage(img,0,0);const a=document.createElement('a');a.href=c.toDataURL('image/png');a.download='plane-view.png';a.click()}

  // Navigation and controls
  $$('.tab').forEach(b=>b.onclick=()=>{$$('.tab').forEach(x=>x.classList.remove('active'));$$('.tab-pane').forEach(x=>x.classList.remove('active'));b.classList.add('active');$(`#tab-${b.dataset.tab}`).classList.add('active')});
  $('#closePanel').onclick=()=>$('#sidePanel').classList.add('closed');$('#panelToggle').onclick=()=>$('#sidePanel').classList.toggle('closed');
  $('#gridToggle').onclick=()=>{state.grid=!state.grid;render()};$('#perspectiveToggle').onclick=()=>{state.perspective=!state.perspective;render()};$('#orientationToggle').onclick=()=>{if(state.orientation==='landscape'){const wrap=$('#canvasWrap'),wr=wrap.getBoundingClientRect(),cr=els.canvas.getBoundingClientRect();state.landscapeLeft=cr.left-wr.left}setOrientation(state.orientation==='landscape'?'portrait':'landscape')};
  $('#undoBtn').onclick=undo;$('#redoBtn').onclick=redo;$('#saveBtn').onclick=saveProject;$('#openBtn').onclick=()=>$('#projectInput').click();$('#captureBtn').onclick=capture;
  $('#fullscreenBtn').onclick=()=>document.fullscreenElement?document.exitFullscreen():document.documentElement.requestFullscreen();$('#fitBtn').onclick=()=>{state.view={zoom:1,x:0,y:0,rotation:0};applyView()};
  window.addEventListener('resize',()=>{if(state.orientation==='portrait')state.landscapeLeft=null;positionCanvasForOrientation()});
  $('#imageUploadBtn').onclick=()=>$('#imageInput').click();$('#imageInput').onchange=async e=>{const f=e.target.files[0];if(!f)return;try{const out=await trimImage(f);addItem({kind:'image',name:f.name.replace(/\.[^.]+$/,''),data:out.data,w:300,h:300/out.ratio})}catch(err){alert('이미지를 불러오지 못했습니다.')}e.target.value=''};
  $('#projectInput').onchange=async e=>{const f=e.target.files[0];if(!f)return;try{const d=JSON.parse(await f.text());snapshot();state.items=d.items||[];state.guides=d.guides||[];state.view=d.view||state.view;setOrientation(d.orientation||'landscape',false);orderSeed=Math.max(0,...state.items.map(i=>i.order||0));state.selected=[];render()}catch(err){alert('올바른 PLANE 프로젝트 파일이 아닙니다.')}e.target.value=''};
  $$('#shapeGrid button').forEach(b=>b.onclick=()=>{$$('#shapeGrid button').forEach(x=>x.classList.remove('active'));b.classList.add('active');selectedShape=b.dataset.shape});$('#curveAmount').oninput=e=>$('#curveValue').value=e.target.value+'%';$('#createShapeBtn').onclick=createShape;
  $$('.guide-grid button').forEach(b=>b.onclick=()=>{snapshot();const bounds=editingBounds(),g={id:uid(),type:b.dataset.guide,x:bounds.cx,y:bounds.cy,angle:0,radius:100,visible:true,locked:false};state.guides.push(g);state.selectedGuide=g.id;render()});$('#snapToggle').onchange=e=>state.snap=e.target.checked;$('#guidesToggle').onchange=e=>{state.guidesVisible=e.target.checked;renderGuides()};
  $$('[data-guide-rotate]').forEach(b=>b.onclick=()=>{const g=state.guides.find(x=>x.id===state.selectedGuide);if(!g||g.type==='circle'||g.locked)return;snapshot();g.angle=((g.angle||0)+(+b.dataset.guideRotate))%360;renderGuides()});
  $('#guideRadius').oninput=e=>{const g=state.guides.find(x=>x.id===state.selectedGuide);if(!g)return;g.radius=px(e.target.value);renderGuides()};$('#guideRadius').onchange=()=>snapshot();
  $$('#textureGrid button').forEach(b=>b.onclick=()=>{updateSelected(i=>i.texture=b.dataset.texture)});$('#textureStrength').oninput=e=>{$('#textureValue').value=e.target.value+'%';selectedItems().forEach(i=>i.textureStrength=e.target.value/100);renderMaterials()};$('#textureStrength').onchange=()=>snapshot();$('#materialOpacity').oninput=e=>{$('#opacityValue').value=e.target.value+'%';selectedItems().forEach(i=>i.opacity=e.target.value/100);renderMaterials()};$('#materialOpacity').onchange=()=>snapshot();$('#shadowToggle').onchange=e=>updateSelected(i=>i.shadow=e.target.checked);
  $$('.boolean-grid button').forEach(b=>b.onclick=()=>beginBoolean(b.dataset.op));$('#booleanCancel').onclick=cancelBoolean;$('#booleanApply').onclick=applyBoolean;
  ['posX','posY','itemWidth','itemHeight','itemRotation'].forEach(id=>$('#'+id).onchange=e=>{const item=primary();if(!item)return;snapshot();if(id==='posX')item.x=px(e.target.value);if(id==='posY')item.y=px(e.target.value);if(id==='itemWidth'){const old=item.w;item.w=px(e.target.value);if(item.keepRatio)item.h*=item.w/old}if(id==='itemHeight'){const old=item.h;item.h=px(e.target.value);if(item.keepRatio)item.w*=item.h/old}if(id==='itemRotation')item.rotation=+e.target.value;render()});$('#ratioToggle').onchange=e=>updateSelected(i=>i.keepRatio=e.target.checked);
  $$('[data-rotate]').forEach(b=>b.onclick=()=>rotateSelected(+b.dataset.rotate));$('#sendBack').onclick=()=>updateSelected(i=>moveLayerSmart(i,'back'));$('#bringFront').onclick=()=>updateSelected(i=>moveLayerSmart(i,'front'));$$('[data-align]').forEach(b=>b.onclick=()=>alignItems(b.dataset.align));
  $('#viewZoom').oninput=e=>{state.view.zoom=e.target.value/100;applyView()};$$('[data-pan]').forEach(b=>b.onclick=()=>{const [x,y]=b.dataset.pan.split(',').map(Number);state.view.x+=x;state.view.y+=y;applyView()});$$('[data-view-rotate]').forEach(b=>b.onclick=()=>{state.view.rotation=(state.view.rotation+(+b.dataset.viewRotate)+360)%360;applyView()});$('#viewReset').onclick=$('#fitBtn').onclick;
  $('#canvasWrap').addEventListener('wheel',e=>{const item=primary();if(!item||item.locked)return;e.preventDefault();if(!wheelSizingActive){snapshot();wheelSizingActive=true}clearTimeout(wheelSizingTimer);wheelSizingTimer=setTimeout(()=>{wheelSizingActive=false},180);const scale=Math.exp(-e.deltaY*.0015);item.w=clamp(item.w*scale,5,5000);item.h=clamp(item.h*scale,5,5000);renderMaterials();renderSelection();updateInspector();renderList()},{passive:false});
  document.addEventListener('keydown',e=>{if(['INPUT','TEXTAREA'].includes(document.activeElement.tagName))return;if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='z'){e.preventDefault();e.shiftKey?redo():undo();return}if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='y'){redo();return}if(e.key==='Escape'){cancelBoolean();state.selected=[];render();return}if(e.key==='Delete'){if(selectedItems().some(i=>!i.locked)){snapshot();state.items=state.items.filter(i=>!state.selected.includes(i.id)||i.locked);state.selected=[];render()}return}const d=e.shiftKey?10:1,dirs={ArrowLeft:[-d,0],ArrowRight:[d,0],ArrowUp:[0,-d],ArrowDown:[0,d]};if(dirs[e.key]){e.preventDefault();snapshot();const [x,y]=dirs[e.key];selectedItems().forEach(i=>{if(!i.locked){i.x+=x;i.y+=y}});render()}});

  // Starter composition makes the prototype understandable on first launch.
  state.items=[
    {id:uid(),kind:'rect',name:'검정 정사각형',x:390,y:355,w:250,h:250,radius:0,rotation:0,layer:0,order:++orderSeed,fill:'#111111',stroke:'none',strokeWidth:0,opacity:1,texture:'basic',textureStrength:.45,shadow:false,locked:false,visible:true,keepRatio:true},
    {id:uid(),kind:'ellipse',name:'중간 회색 원',x:650,y:355,w:220,h:220,rotation:0,layer:1,order:++orderSeed,fill:'#777777',stroke:'none',strokeWidth:0,opacity:1,texture:'basic',textureStrength:.45,shadow:false,locked:false,visible:true,keepRatio:true},
    {id:uid(),kind:'line',name:'굵은 검정 선',x:520,y:560,w:420,h:22,rotation:0,layer:2,order:++orderSeed,fill:'#111111',stroke:'none',strokeWidth:22,opacity:1,texture:'basic',textureStrength:.45,shadow:false,locked:false,visible:true,keepRatio:true}
  ];
  state.selected=[state.items[1].id]; render();
})();
