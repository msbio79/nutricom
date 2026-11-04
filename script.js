/**
 * ============================================================================
 * 생체 분자의 탈수 축합 & 가수분해 반응 시뮬레이션
 * - 교과서 화학식(하워스 투영식) / 간편 모형 두 가지 표시 모드
 * - 자석 스냅(탈수 축합, H₂O 1회 방출)
 * - 더블클릭/더블탭 분리(가수분해, H₂O 첨가) 및 단독 분자 삭제
 * - 단계별 진행(이전 / 다음 / 자동 재생)
 * - Pointer Events 기반 마우스·터치·펜(애플 펜슬) 통합 입력, 펜슬 사용 중 손바닥 무시
 * - 판서: 펜 · 레이저 포인터(잠시 후 서서히 사라짐) · 지우개
 * ============================================================================
 */

(function () {
  'use strict';

  // --------------------------------------------------------------------------
  // 1. 20종 아미노산 데이터
  // --------------------------------------------------------------------------
  const AMINO_ACIDS = [
    { code: 'Gly', name: '글리신', rGroup: '— H', type: 'np' },
    { code: 'Ala', name: '알라닌', rGroup: '— CH₃', type: 'np' },
    { code: 'Val', name: '발린', rGroup: '— CH(CH₃)₂', type: 'np' },
    { code: 'Leu', name: '류신', rGroup: '— CH₂CH(CH₃)₂', type: 'np' },
    { code: 'Ile', name: '아이소류신', rGroup: '— CH(CH₃)CH₂CH₃', type: 'np' },
    { code: 'Pro', name: '프롤린', rGroup: '—(CH₂)₃— N과 고리', type: 'np' },
    { code: 'Phe', name: '페닐알라닌', rGroup: '— CH₂—C₆H₅', type: 'np' },
    { code: 'Tyr', name: '티로신', rGroup: '— CH₂—C₆H₄—OH', type: 'p' },
    { code: 'Trp', name: '트립토판', rGroup: '인돌 고리', type: 'np' },
    { code: 'Ser', name: '세린', rGroup: '— CH₂OH', type: 'p' },
    { code: 'Thr', name: '트레오닌', rGroup: '— CH(OH)CH₃', type: 'p' },
    { code: 'Cys', name: '시스테인', rGroup: '— CH₂SH', type: 'p' },
    { code: 'Met', name: '메티오닌', rGroup: '— (CH₂)₂SCH₃', type: 'np' },
    { code: 'Asn', name: '아스파라긴', rGroup: '— CH₂CONH₂', type: 'p' },
    { code: 'Gln', name: '글루타민', rGroup: '— (CH₂)₂CONH₂', type: 'p' },
    { code: 'Asp', name: '아스파트산', rGroup: '— CH₂COO⁻', type: 'ac' },
    { code: 'Glu', name: '글루탐산', rGroup: '— (CH₂)₂COO⁻', type: 'ac' },
    { code: 'Lys', name: '리신', rGroup: '— (CH₂)₄NH₃⁺', type: 'ba' },
    { code: 'Arg', name: '아르기닌', rGroup: '— 구아니디노기', type: 'ba' },
    { code: 'His', name: '히스티딘', rGroup: '이미다졸 고리', type: 'ba' }
  ];

  const AA_SIMPLE_COLORS = { np: '#fde68a', p: '#a7f3d0', ac: '#fecaca', ba: '#bfdbfe' };

  // --------------------------------------------------------------------------
  // 2. 전역 상태
  // --------------------------------------------------------------------------
  const state = {
    theme: 'light',
    activeCategory: 'carbs',
    displayMode: 'formula', // 'formula' | 'simple'
    showBondLabels: false,  // 결합 이름표 표시 여부 (기본: 숨기기)
    showWater: true,        // 물 분자(H₂O) 애니메이션 표시 여부
    showCH: false,          // 생략된 탄소(C)·수소(H) 표시 여부 (구조식 모드)

    view: { scale: 1.0, offsetX: 0, offsetY: 0, minScale: 0.4, maxScale: 5.0 },

    width: 0,
    height: 0,
    dpr: window.devicePixelRatio || 1,

    // 판서
    drawMode: false,
    penColor: '#ef4444',
    penWidth: 3,
    isEraser: false,
    isLaser: false,     // 레이저 포인터: 쓴 뒤 잠시 후 서서히 사라지는 필기
    strokes: [],
    laserStrokes: [],   // 사라지는 중인 레이저 필기
    lastLaserEnd: 0,    // 마지막 레이저 필기를 끝낸 시각 (이어 쓰는 동안은 함께 유지)
    currentStroke: null,

    // 개체
    molecules: [],
    bonds: [],          // [{ id, type, mol1, mol2, slot, label }] (형성 순서대로 쌓임)
    waterParticles: [],
    slides: [],         // 가수분해 후 분자가 벌어지는 애니메이션
    history: [],        // '이전 단계'용 기록: { type: 'add', mols } | { type: 'bond', bond }

    // 상호작용
    pointers: new Map(),
    isPinching: false,
    lastPinchDist: null,
    lastPinchCenter: null,
    draggedMol: null,
    dragOffset: { x: 0, y: 0 },
    dragMoved: false,   // 누른 뒤 실제로 움직였는가 (단순 클릭과 드래그 구분)
    downScreen: { x: 0, y: 0 },
    isPanning: false,
    panStart: { x: 0, y: 0 },
    lastTap: { time: 0, mol: null, x: 0, y: 0 },
    recentSplits: [],   // 방금 끊어진 결합 (동시에 여러 결합을 분리할 때 사슬 정렬 유지용)
    stepCache: { key: '', more: false },

    // 단계 진행
    currentPreset: null,
    autoPlaying: false,
    autoTimer: null,
    lastStepText: '',
    lastPresetShown: undefined,

    // 상수
    SNAP_DIST: 45,        // 자석 스냅 감지 거리: 결합 위치에서 이 거리 안(= 분자가 실제로 맞닿을 정도)일 때만 결합
    BOND_OFFSET: { carbs: 180, protein: 150 }, // 결합 시 두 분자 중심 간격 (결합선을 짧게)
    ESTER_OFFSET_X: 150,  // 지질: 글리세롤 중심 ~ 지방산 중심 간격
    PHOSPHATE_OFFSET_X: 110, // 지질: 인산기 HO를 글리세롤 오른쪽 OH에 겹쳐 놓는 위치 (결합 감지)
    PHOSPHATE_BOND_X: -120,  // 지질: 결합 후 인산기 위치 (글리세롤 왼쪽 = 지방산 반대편)
    PHOSPHATE_R: 32,      // 인산기 원 반지름
    SEPARATE_SHIFT: 150,  // 가수분해 후 떼어놓는 거리 (SNAP_DIST보다 커야 바로 다시 붙지 않음)
    SPAWN_GAP: 110,       // 새 분자를 기존 분자 오른쪽에 배치할 때 두 분자 테두리 사이 간격
    AUTO_INTERVAL: 3000    // 자동 재생 간격 (물 분자가 빠져나가는 모습을 볼 수 있도록)
  };

  // --------------------------------------------------------------------------
  // 3. DOM
  // --------------------------------------------------------------------------
  const $ = (id) => document.getElementById(id);
  const dom = {
    body: document.body,
    sidebar: $('sidebar'),
    themeToggleBtn: $('themeToggleBtn'),
    collapseSidebarBtn: $('collapseSidebarBtn'),
    expandSidebarBtn: $('expandSidebarBtn'),
    quickClearBtn: $('quickClearBtn'),

    catTabs: document.querySelectorAll('.cat-tab'),
    panels: { carbs: $('carbs-panel'), protein: $('protein-panel'), lipid: $('lipid-panel'), free: $('free-panel') },
    freeAminoPalette: $('freeAminoPalette'),
    modeFormulaBtn: $('modeFormulaBtn'),
    modeSimpleBtn: $('modeSimpleBtn'),
    labelOnBtn: $('labelOnBtn'),
    labelOffBtn: $('labelOffBtn'),
    waterOnBtn: $('waterOnBtn'),
    waterOffBtn: $('waterOffBtn'),
    chOnBtn: $('chOnBtn'),
    chOffBtn: $('chOffBtn'),

    stepPrevBtn: $('stepPrevBtn'),
    stepNextBtn: $('stepNextBtn'),
    stepPlayBtn: $('stepPlayBtn'),
    stepStatus: $('stepStatus'),
    miniPrevBtn: $('miniPrevBtn'),
    miniPlayBtn: $('miniPlayBtn'),
    miniNextBtn: $('miniNextBtn'),
    miniStepText: $('miniStepText'),

    separateBondsBtn: $('separateBondsBtn'),
    clearAllMolsBtn: $('clearAllMolsBtn'),

    zoomInBtn: $('zoomInBtn'),
    zoomOutBtn: $('zoomOutBtn'),
    zoomResetBtn: $('zoomResetBtn'),
    drawModeBtn: $('drawModeBtn'),
    drawOptionsPanel: $('drawOptionsPanel'),
    colorDots: document.querySelectorAll('.color-dot'),
    widthBtns: document.querySelectorAll('.width-btn'),
    eraserBtn: $('eraserBtn'),
    laserBtn: $('laserBtn'),
    clearDrawBtn: $('clearDrawBtn'),

    canvasWrapper: $('canvas-wrapper'),
    simCanvas: $('simCanvas'),
    drawCanvas: $('drawCanvas'),
    zoomIndicator: $('zoomIndicator'),
    hintText: $('hintText'),
    hintBar: $('hintBar'),
    showHintBtn: $('showHintBtn'),
    aminoPalette: $('aminoPalette')
  };

  const simCtx = dom.simCanvas.getContext('2d');
  const drawCtx = dom.drawCanvas.getContext('2d');

  // --------------------------------------------------------------------------
  // 4. 초기화 & 뷰포트
  // --------------------------------------------------------------------------
  function init() {
    setupAminoAcidPalette();
    bindEventListeners();
    // 좁은 화면(휴대폰)에서는 메뉴가 캔버스를 덮으므로 접은 상태로 시작
    if (window.matchMedia && window.matchMedia('(max-width: 768px)').matches) {
      dom.sidebar.classList.add('collapsed');
    }
    resizeCanvases();
    window.addEventListener('resize', resizeCanvases);
    // 메뉴가 접히는 애니메이션 동안에도 캔버스 크기 변화를 따라가며 가운데 유지
    if (typeof ResizeObserver !== 'undefined') {
      new ResizeObserver(() => resizeCanvases()).observe(dom.canvasWrapper);
    }

    loadPreset('maltose');
    requestAnimationFrame(renderLoop);
  }

  function resizeCanvases() {
    const rect = dom.canvasWrapper.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    if (rect.width === state.width && rect.height === state.height && dpr === state.dpr) return;

    // 크기가 바뀌어도(메뉴 접기/펼치기, 창 크기 변경) 화면 가운데에 보던 지점이 계속 가운데에 오도록
    if (state.width > 0 && state.height > 0) {
      state.view.offsetX += (rect.width - state.width) / 2;
      state.view.offsetY += (rect.height - state.height) / 2;
    }
    state.width = rect.width;
    state.height = rect.height;
    state.dpr = dpr;

    [dom.simCanvas, dom.drawCanvas].forEach(c => {
      c.width = state.width * state.dpr;
      c.height = state.height * state.dpr;
      c.style.width = state.width + 'px';
      c.style.height = state.height + 'px';
    });

    updateZoomIndicator();
    renderDrawCanvas();
  }

  function screenToWorld(sx, sy) {
    return {
      x: (sx - state.view.offsetX) / state.view.scale,
      y: (sy - state.view.offsetY) / state.view.scale
    };
  }

  function clientToScreen(clientX, clientY) {
    const rect = dom.canvasWrapper.getBoundingClientRect();
    return { x: clientX - rect.left, y: clientY - rect.top };
  }

  function zoomAt(factor, px, py) {
    const newScale = Math.min(state.view.maxScale, Math.max(state.view.minScale, state.view.scale * factor));
    if (newScale === state.view.scale) return;

    const wb = screenToWorld(px, py);
    state.view.scale = newScale;
    state.view.offsetX = px - wb.x * state.view.scale;
    state.view.offsetY = py - wb.y * state.view.scale;

    updateZoomIndicator();
    renderDrawCanvas();
  }

  // 화면 맞춤: 모든 분자가 보이도록 배율·위치 조정
  function fitView() {
    if (state.molecules.length === 0) {
      state.view.scale = 1.0;
      state.view.offsetX = state.width / 2;
      state.view.offsetY = state.height / 2;
    } else {
      let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
      state.molecules.forEach(m => {
        minX = Math.min(minX, m.x - m.width / 2);
        const nameExtra = (m.subType === 'fatty_sat' || m.subType === 'fatty_unsat') ? 100 : 0;
        maxX = Math.max(maxX, m.x + m.width / 2 + nameExtra);
        minY = Math.min(minY, m.y - m.height / 2);
        maxY = Math.max(maxY, m.y + m.height / 2);
      });
      const padX = 60, padY = 70;
      const bw = (maxX - minX) + padX * 2;
      const bh = (maxY - minY) + padY * 2;
      const availW = Math.max(200, state.width - 40);
      const availH = Math.max(200, state.height - 150); // 상단 툴바 + 하단 힌트 여백
      const scale = Math.min(state.view.maxScale, Math.max(state.view.minScale, Math.min(availW / bw, availH / bh, 1.2)));
      const cx = (minX + maxX) / 2;
      const cy = (minY + maxY) / 2;
      state.view.scale = scale;
      state.view.offsetX = state.width / 2 - cx * scale;
      state.view.offsetY = state.height / 2 + 5 - cy * scale;
    }
    updateZoomIndicator();
    renderDrawCanvas();
  }

  function updateZoomIndicator() {
    dom.zoomIndicator.textContent = Math.round(state.view.scale * 100) + '%';
  }

  // --------------------------------------------------------------------------
  // 5. 분자 데이터 모델
  // --------------------------------------------------------------------------
  class Molecule {
    constructor(config) {
      this.id = 'mol_' + Math.random().toString(36).slice(2, 11);
      this.category = config.category || 'carbs';
      this.subType = config.subType || 'glucose';
      this.name = config.name || '포도당';
      this.x = config.x || 0;
      this.y = config.y || 0;
      this.width = config.width || 170;
      this.height = config.height || 170;
      this.data = config.data || {};
      this.groupId = this.id; // 연결된 복합체 묶음 ID
    }

    containsPoint(wx, wy) {
      return (
        wx >= this.x - this.width / 2 && wx <= this.x + this.width / 2 &&
        wy >= this.y - this.height / 2 && wy <= this.y + this.height / 2
      );
    }

    // 오른쪽 반응 부위(단당류 1번 C / 카복실기)가 결합되었는가
    isRightBonded() {
      return state.bonds.some(b => b.mol1 === this && b.type !== 'ester');
    }

    // 왼쪽 반응 부위(단당류 4번 C·과당 2번 C / 아미노기)가 결합되었는가
    isLeftBonded() {
      return state.bonds.some(b => b.mol2 === this);
    }
  }

  // 단당류 생성 헬퍼 (anomer: α/β, flipped: 셀룰로오스용 상하 반전)
  function makeCarb(subType, x, y, extra = {}) {
    const names = { glucose: '포도당', fructose: '과당', galactose: '갈락토스' };
    const defaultAnomer = subType === 'galactose' ? 'beta' : 'alpha';
    return new Molecule({
      category: 'carbs',
      subType,
      name: extra.name || names[subType],
      x, y,
      data: { anomer: extra.anomer || defaultAnomer, flipped: !!extra.flipped }
    });
  }

  function makeAmino(aa, x, y) {
    return new Molecule({ category: 'protein', subType: 'amino', name: aa.name, x, y, width: 150, data: aa });
  }

  function makeLipidPart(subType, x, y, name) {
    const spec = {
      glycerol: { name: '글리세롤', width: 140, height: 300 },
      fatty_sat: { name: '포화 지방산', width: 230, height: 50 },
      fatty_unsat: { name: '불포화 지방산', width: 230, height: 50, data: { kink: true } },
      phosphate: { name: '인산기', width: 140, height: 80 }
    }[subType];
    return new Molecule({
      category: 'lipid', subType, x, y,
      name: name || spec.name, width: spec.width, height: spec.height, data: spec.data || {}
    });
  }

  // 인지질 2중층 단위 크기
  const PL_UNIT = { HEAD_R: 22, LEN: 160, LAYER_GAP: 14, HEAD_GAP: 6, COUNT: 40 };

  const flipY = (m) => (m.data && m.data.flipped ? -1 : 1);
  // 1번 탄소 반응 OH 방향 (+1 아래 / -1 위): α는 아래, β는 위, 상하 반전 시 뒤집힘
  const c1Dir = (m) => (m.data.anomer === 'beta' ? -1 : 1) * flipY(m);

  // --------------------------------------------------------------------------
  // 6. 물 분자 파티클
  // --------------------------------------------------------------------------
  // 물 분자 애니메이션 시간 (ms) - 학생들이 충분히 볼 수 있도록 천천히
  const WATER_TIMING = {
    // 탈수: 나타나서 사라질 때까지 전체 2초 (= OUT_MOVE + OUT_HOLD + OUT_FADE)
    OUT_MOVE: 800,   // 탈수: 결합 부위에서 위쪽으로 빠져나가는 시간
    OUT_HOLD: 900,   // 탈수: 빠져나간 뒤 위쪽에 머무는 시간
    OUT_FADE: 300,   // 탈수: 서서히 사라지는 시간
    IN_MOVE: 1400,   // 가수분해: 위에서 결합 부위로 천천히 들어오는 시간
    IN_FADE: 500     // 가수분해: 결합 부위에 흡수되며 사라지는 시간
  };
  const nowMs = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());
  const easeOutCubic = (p) => 1 - Math.pow(1 - p, 3);
  const easeInOutSine = (p) => -(Math.cos(Math.PI * p) - 1) / 2;

  // 물 분자(라벨 포함)가 어떤 분자와도 겹치지 않는 결합 부위 위쪽 높이 찾기
  function findWaterRestY(x, y) {
    const HALF_W = 90;  // 라벨 "💧 H₂O 방출 (탈수 축합)" 절반 폭
    const UP = 52;      // 중심 ~ 라벨 윗부분
    const DOWN = 24;    // 중심 ~ 산소 원 아랫부분
    const MARGIN = 10;
    let cy = y - 90;
    for (let i = 0; i < 30; i++) {
      const hit = state.molecules.find(m =>
        Math.abs(m.x - x) < m.width / 2 + HALF_W &&
        cy + DOWN > m.y - m.height / 2 &&
        cy - UP < m.y + m.height / 2
      );
      if (!hit) break;
      cy = hit.y - hit.height / 2 - DOWN - MARGIN;
    }
    return cy;
  }

  class WaterParticle {
    constructor(startX, startY, mode = 'outward') {
      this.mode = mode;
      this.born = nowMs();
      this.originX = startX;
      this.originY = startY;
      if (mode === 'outward') {
        // 결합 부위 → 바로 위쪽, 분자 그림을 가리지 않는 빈 공간까지 이동해 머무름
        this.restX = startX;
        this.restY = findWaterRestY(startX, startY);
        this.x = startX;
        this.y = startY;
        this.scale = 0.3;
      } else {
        this.fromY = startY - 110;
        this.x = startX;
        this.y = this.fromY;
        this.scale = 1.0;
      }
      this.opacity = 1.0;
      this.rotation = 0;
      this.isAlive = true;
    }

    update() {
      const t = nowMs() - this.born;
      const T = WATER_TIMING;

      if (this.mode === 'outward') {
        if (t < T.OUT_MOVE) {
          // 1단계: 천천히 빠져나감 (점점 커지며)
          const p = easeOutCubic(t / T.OUT_MOVE);
          this.x = this.originX + (this.restX - this.originX) * p;
          this.y = this.originY + (this.restY - this.originY) * p;
          this.scale = 0.3 + 0.7 * p;
          this.rotation = Math.sin(t / 300) * 0.15;
          this.opacity = 1;
        } else if (t < T.OUT_MOVE + T.OUT_HOLD) {
          // 2단계: 옆에 머무름 (살짝 떠 있는 느낌)
          const h = t - T.OUT_MOVE;
          this.x = this.restX;
          this.y = this.restY + Math.sin(h / 450) * 3;
          this.scale = 1;
          this.rotation = Math.sin(h / 600) * 0.08;
          this.opacity = 1;
        } else {
          // 3단계: 서서히 사라짐
          const f = (t - T.OUT_MOVE - T.OUT_HOLD) / T.OUT_FADE;
          this.opacity = 1 - f;
          this.y = this.restY - f * 12;
          if (f >= 1) this.isAlive = false;
        }
      } else {
        // 도착 전에는 결합 부위를 따라감 (분자를 끌고 있어도 정확히 결합 부위로 들어감)
        if (!this.arrived && this.bond && state.bonds.includes(this.bond)) {
          const site = bondSite(this.bond);
          this.fromY += site.y - this.originY;
          this.originX = site.x;
          this.originY = site.y;
          this.x = site.x;
        }
        if (t < T.IN_MOVE) {
          // 위에서 결합 부위로 천천히 들어옴
          const p = easeInOutSine(t / T.IN_MOVE);
          this.y = this.fromY + (this.originY - this.fromY) * p;
          this.rotation = Math.sin(t / 300) * 0.15;
        } else {
          // 결합 부위에 도착한 순간 결합이 끊어짐
          if (!this.arrived) {
            this.arrived = true;
            if (this.onArrive) this.onArrive();
          }
          // 결합 부위에 흡수되며 작아짐
          const f = (t - T.IN_MOVE) / T.IN_FADE;
          this.y = this.originY;
          this.scale = Math.max(0.05, 1 - f);
          this.opacity = 1 - f;
          if (f >= 1) this.isAlive = false;
        }
      }
    }

    draw(ctx, isDark) {
      ctx.save();
      ctx.translate(this.x, this.y);
      ctx.scale(this.scale, this.scale);
      ctx.rotate(this.rotation);
      ctx.globalAlpha = Math.max(0, this.opacity);

      const atom = (x, y, r, fill, label, font) => {
        ctx.beginPath();
        ctx.arc(x, y, r, 0, Math.PI * 2);
        ctx.fillStyle = fill;
        ctx.fill();
        ctx.lineWidth = 2.5;
        ctx.strokeStyle = '#ffffff';
        ctx.stroke();
        ctx.fillStyle = '#ffffff';
        ctx.font = font;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText(label, x, y);
      };
      atom(0, 0, 18, '#ef4444', 'O', 'bold 15px sans-serif');
      atom(-16, -16, 12, '#22c55e', 'H', 'bold 12px sans-serif');
      atom(16, -16, 12, '#22c55e', 'H', 'bold 12px sans-serif');

      ctx.rotate(-this.rotation);
      ctx.fillStyle = this.mode === 'outward' ? (isDark ? '#38bdf8' : '#0284c7') : '#16a34a';
      ctx.font = 'bold 15.5px sans-serif';
      ctx.fillText(this.mode === 'outward' ? '💧 H₂O 방출 (탈수 축합)' : '💧 H₂O 첨가 (가수분해)', 0, -34);
      ctx.restore();
    }
  }

  const emitWaterOutward = (x, y) => state.waterParticles.push(new WaterParticle(x, y, 'outward'));

  // --------------------------------------------------------------------------
  // 7. 결합 가능성 판정 (드래그 스냅 & 단계 진행 공용)
  // --------------------------------------------------------------------------
  // 사슬형(탄수화물·단백질): L의 오른쪽 부위 + R의 왼쪽 부위
  function planChain(L, R) {
    if (L.category === 'carbs' && L.subType === 'fructose') return null; // 과당은 오른쪽 반응 부위 없음
    if (L.isRightBonded() || R.isLeftBonded()) return null;
    const targetX = L.x + state.BOND_OFFSET[L.category];
    const targetY = L.y;
    return {
      type: L.category === 'carbs' ? 'glycosidic' : 'peptide',
      left: L, right: R, mover: R, slot: null,
      targetX, targetY,
      dist: Math.hypot(R.x - targetX, R.y - targetY)
    };
  }

  // 지질: 글리세롤의 빈 OH 슬롯 + 지방산(카복실기) / 인산기(3번 C에만)
  function planEster(a, b) {
    let gly = null, other = null;
    if (a.subType === 'glycerol') { gly = a; other = b; }
    else if (b.subType === 'glycerol') { gly = b; other = a; }
    if (!gly) return null;

    const isFA = other.subType === 'fatty_sat' || other.subType === 'fatty_unsat';
    const isP = other.subType === 'phosphate';
    if (!isFA && !isP) return null;
    if (state.bonds.some(bd => bd.mol2 === other)) return null; // 이미 다른 곳에 결합됨

    const slots = isP ? [-75, 75] : [-75, 0, 75]; // 인산기는 양 끝 탄소(1번·3번 C)에만
    const offsetX = isP ? state.PHOSPHATE_OFFSET_X : state.ESTER_OFFSET_X;
    let best = null;
    slots.forEach(slot => {
      if (state.bonds.some(bd => bd.mol1 === gly && bd.slot === slot)) return;
      const targetY = gly.y + slot;
      let targetX = gly.x + offsetX;
      let dist = Math.hypot(other.x - targetX, other.y - targetY);
      if (isP) {
        // 인산기: 결합하면 지방산의 반대편(글리세롤 왼쪽)으로 이동
        const leftX = gly.x + state.PHOSPHATE_BOND_X;
        dist = Math.min(dist, Math.hypot(other.x - leftX, other.y - targetY));
        targetX = leftX;
      }
      if (!best || dist < best.dist) {
        best = { type: 'ester', left: gly, right: other, mover: other, slot, targetX, targetY, dist };
      }
    });
    return best;
  }

  function planFor(a, b, allowSwap) {
    if (a === b || a.groupId === b.groupId || a.category !== b.category) return null;
    if (a.category === 'lipid') return planEster(a, b);
    const [L, R] = a.x <= b.x ? [a, b] : [b, a];
    let p = planChain(L, R);
    if (!p && allowSwap) p = planChain(R, L);
    return p;
  }

  function glycosidicLabel(L, R) {
    const a = L.data.anomer === 'beta' ? 'β' : 'α';
    const second = R.subType === 'fructose' ? 'β-2' : '4';
    return `${a}-1,${second}\n글리코시드 결합`;
  }

  function formBond(plan, quiet) {
    const { left, right, mover } = plan;
    moveGroup(mover.groupId, plan.targetX - mover.x, plan.targetY - mover.y);

    let label;
    if (plan.type === 'glycosidic') label = glycosidicLabel(left, right);
    else if (plan.type === 'peptide') label = '펩타이드 결합\n(-CO-NH-)';
    else label = right.subType === 'phosphate' ? '인산\n에스터 결합' : '에스터 결합\n(-COO-)';

    const bond = {
      id: `${left.id}_${right.id}`,
      type: plan.type,
      mol1: left,
      mol2: right,
      slot: plan.slot,
      label
    };
    state.bonds.push(bond);
    state.history.push({ type: 'bond', bond });
    mergeGroups(left.groupId, right.groupId);

    const site = bondSite(bond);
    emitWaterOutward(site.x, site.y);

    if (!quiet) {
      const names = { glycosidic: '글리코시드', peptide: '펩타이드', ester: '에스터' };
      const extra = plan.type === 'ester' && right.subType === 'phosphate'
        ? ' 인산기는 지방산 반대편(친수성 머리 쪽)에 자리 잡습니다.' : '';
      showHint(`✨ ${names[plan.type]} 결합 완성! 물 분자(H₂O)가 1개 방출되었습니다. (탈수 축합)${extra}`);
    }
    return bond;
  }

  // 드래그 중인 묶음의 모든 분자에 대해 가장 가까운 결합 후보 탐색
  function checkAndPerformMagneticSnap(dragged) {
    if (!dragged) return false;
    const members = state.molecules.filter(m => m.groupId === dragged.groupId);
    let best = null;
    for (const a of members) {
      for (const b of state.molecules) {
        if (b.groupId === dragged.groupId) continue;
        const p = planFor(a, b, false);
        if (p && p.dist < state.SNAP_DIST && (!best || p.dist < best.dist)) best = p;
      }
    }
    if (!best) return false;
    formBond(best);
    return true;
  }

  // 글리세롤 근처에 놓았는데 붙을 자리가 없으면 이유를 안내
  function explainNoBond(mol) {
    // 다른 종류(당·아미노산·지질) 분자 옆에 놓은 경우 (자유 모드)
    const otherKind = state.molecules.find(o =>
      o !== mol && o.category !== mol.category && o.subType !== 'pl_unit' &&
      Math.abs(o.x - mol.x) < (o.width + mol.width) / 2 + 30 && Math.abs(o.y - mol.y) < (o.height + mol.height) / 2);
    if (otherKind) {
      const kind = { carbs: '단당류', protein: '아미노산', lipid: '지질 성분' };
      showHint(`⚠️ ${kind[mol.category]}과(와) ${kind[otherKind.category]}은(는) 서로 결합하지 않아요. 같은 종류끼리 맞닿게 해보세요.`);
      return;
    }
    if (mol.category !== 'lipid') return;
    const isP = mol.subType === 'phosphate';
    const isFA = mol.subType === 'fatty_sat' || mol.subType === 'fatty_unsat';
    if (!isP && !isFA) return;
    if (state.bonds.some(b => b.mol2 === mol)) return;
    // 인산기는 글리세롤 오른쪽(OH에 겹침)과 왼쪽(결합 후 자리) 모두 결합 위치로 인정되므로 둘 다 확인
    const offs = isP ? [state.PHOSPHATE_OFFSET_X, state.PHOSPHATE_BOND_X] : [state.ESTER_OFFSET_X];
    let gly = null, nearSlot = null, best = Infinity;
    state.molecules.forEach(g => {
      if (g.subType !== 'glycerol') return;
      [-75, 0, 75].forEach(slot => {
        offs.forEach(off => {
          const d = Math.hypot(mol.x - (g.x + off), mol.y - (g.y + slot));
          if (d < best) { best = d; gly = g; nearSlot = slot; }
        });
      });
    });
    if (!gly || best > 220) return;
    const free = (slot) => !state.bonds.some(b => b.mol1 === gly && b.slot === slot);
    if (isP && nearSlot === 0 && (free(-75) || free(75))) {
      showHint('⚠️ 인산기는 글리세롤의 가운데 탄소에는 결합하지 않아요. 맨 위나 맨 아래 OH에 인산기의 HO를 겹쳐보세요.');
    } else if (isP && !free(-75) && !free(75)) {
      showHint('⚠️ 인산기는 글리세롤의 양 끝 탄소(맨 위·맨 아래)에만 결합합니다. 빈 자리가 없어요. 지방산 하나를 분리해보세요.');
    } else if (isFA && !free(-75) && !free(0) && !free(75)) {
      showHint('⚠️ 글리세롤의 OH 3개가 모두 결합되어 더 붙일 자리가 없습니다.');
    } else {
      showHint('💡 연두색 HO를 글리세롤의 빈 OH에 겹치듯 맞닿게 놓으면 결합합니다.');
    }
  }

  // 단계 진행용: 가장 왼쪽부터, 가까운 순서로 다음 결합 후보 선택
  function findNextPlan() {
    let best = null;
    const mols = state.molecules;
    for (let i = 0; i < mols.length; i++) {
      for (let j = i + 1; j < mols.length; j++) {
        const p = planFor(mols[i], mols[j], true);
        if (!p) continue;
        if (!best ||
            p.left.x < best.left.x - 1 ||
            (Math.abs(p.left.x - best.left.x) <= 1 && p.dist < best.dist)) {
          best = p;
        }
      }
    }
    return best;
  }

  // --------------------------------------------------------------------------
  // 8. 결합 분리 (가수분해)
  // --------------------------------------------------------------------------
  // 1단계: 물 분자가 결합 부위로 들어옴 (결합은 아직 유지)
  function separateBond(bond, quiet) {
    if (!bond || bond.hydrolyzing) return;
    bond.hydrolyzing = true;

    const site = bondSite(bond);
    const water = new WaterParticle(site.x, site.y, 'inward');
    water.bond = bond;
    water.onArrive = () => completeHydrolysis(bond, quiet);
    state.waterParticles.push(water);

    if (!quiet) showHint('💧 물 분자(H₂O)가 결합 부위로 들어가고 있습니다...');
  }

  // 2단계: 물 분자가 도착하면 결합이 끊어지고 두 분자가 천천히 벌어짐
  function completeHydrolysis(bond, quiet) {
    const idx = state.bonds.indexOf(bond);
    if (idx === -1) return;
    const site = bondSite(bond);
    state.bonds.splice(idx, 1);
    recalculateGroups();

    // 방금 끊어진 결합 기록 (1.5초): '결합 분리'로 여러 결합이 동시에 끊어져도 같은 사슬로 취급
    const now = nowMs();
    state.recentSplits = state.recentSplits.filter(s => now - s.time < 1500);
    state.recentSplits.push({ a: bond.mol1, b: bond.mol2, time: now });

    // 끊어진 지점 오른쪽의 같은 줄 분자들을 함께 밀어 사슬 정렬을 유지하고, 바로 다시 붙지 않게 함
    // (왼쪽 분자와 아직 연결된 분자 - 예: 글리세롤의 다른 지방산 - 는 그대로 둠)
    const dir = bond.mol2.x >= bond.mol1.x ? 1 : -1; // 인산기는 글리세롤 왼쪽 → 왼쪽으로 떨어짐
    // 지질(에스터): 떨어진 지방산·인산기 하나만 이동 (위아래 이웃 지방산은 그대로)
    // 사슬(글리코시드·펩타이드): 같은 사슬에서 끊긴 지점 바깥쪽 분자들만 함께 밀어 간격 유지
    //  (같은 줄에 따로 놓인 상관없는 분자는 밀지 않음)
    let mols;
    if (bond.type === 'ester') {
      mols = [bond.mol2];
    } else {
      const chain = chainMembers(bond.mol1);
      mols = state.molecules.filter(m =>
        m === bond.mol2 ||
        (chain.has(m) && m.groupId !== bond.mol1.groupId && m.x * dir > site.x * dir && Math.abs(m.y - bond.mol2.y) < 30)
      );
    }
    state.slides.push({ mols, dist: dir * state.SEPARATE_SHIFT, moved: 0, start: nowMs(), duration: 700 });

    if (!quiet) showHint('💧 결합 분리(가수분해)! 물 분자(H₂O)가 첨가되어 -H와 -OH가 복원되었습니다.');
    else if (!state.bonds.some(b => b.hydrolyzing)) {
      showHint('💧 물 분자(H₂O)가 첨가되어 모든 결합이 분리(가수분해)되었습니다.');
    }
  }

  // 현재 결합 + 방금 끊어진 결합으로 이어진 분자 전체 (같은 사슬)
  function chainMembers(start) {
    const links = state.bonds.map(b => [b.mol1, b.mol2]).concat(state.recentSplits.map(s => [s.a, s.b]));
    const seen = new Set([start]);
    const queue = [start];
    while (queue.length) {
      const cur = queue.pop();
      links.forEach(([a, b]) => {
        const next = a === cur ? b : (b === cur ? a : null);
        if (next && !seen.has(next)) { seen.add(next); queue.push(next); }
      });
    }
    return seen;
  }

  // 분리 후 분자가 미끄러지듯 벌어지는 애니메이션
  function updateSlides() {
    if (state.slides.length === 0) return;
    const now = nowMs();
    state.slides = state.slides.filter(s => {
      const p = Math.min(1, (now - s.start) / s.duration);
      const target = s.dist * easeOutCubic(p);
      const dx = target - s.moved;
      s.mols.forEach(m => { m.x += dx; });
      s.moved = target;
      return p < 1;
    });
  }

  // 진행 중인 가수분해·분리 애니메이션을 즉시 끝냄 (카테고리 전환 시)
  function finishPendingWork() {
    state.waterParticles.forEach(p => {
      if (p.onArrive && !p.arrived) { p.arrived = true; p.onArrive(); }
    });
    state.slides.forEach(s => {
      const rest = s.dist - s.moved;
      s.mols.forEach(m => { m.x += rest; });
    });
    state.slides = [];
    state.waterParticles = [];
  }

  function separateMoleculeBonds(mol) {
    const related = state.bonds.filter(b => b.mol1 === mol || b.mol2 === mol);
    related.forEach(b => separateBond(b));
    return related.length > 0;
  }

  function separateAllBonds() {
    stopAutoPlay();
    const targets = state.bonds.filter(b => !b.hydrolyzing);
    if (targets.length === 0) {
      showHint('분리할 결합이 없습니다.');
      return;
    }
    targets.forEach(b => separateBond(b, true));
    showHint('💧 물 분자(H₂O)가 모든 결합 부위로 들어가고 있습니다...');
  }

  function moveGroup(groupId, dx, dy) {
    state.molecules.forEach(m => {
      if (m.groupId === groupId) { m.x += dx; m.y += dy; }
    });
  }

  function mergeGroups(g1, g2) {
    if (g1 === g2) return;
    state.molecules.forEach(m => { if (m.groupId === g2) m.groupId = g1; });
  }

  function recalculateGroups() {
    // 세포막처럼 고정 묶음(fixedGroup)이 있는 개체는 항상 한 덩어리로 유지
    state.molecules.forEach(m => { m.groupId = (m.data && m.data.fixedGroup) || m.id; });
    state.bonds.forEach(b => mergeGroups(b.mol1.groupId, b.mol2.groupId));
  }

  function removeMolecule(mol) {
    // 세포막 조각은 통째로 삭제
    if (mol.data && mol.data.fixedGroup) {
      const g = mol.data.fixedGroup;
      state.molecules = state.molecules.filter(m => !(m.data && m.data.fixedGroup === g));
      showHint('세포막(인지질 2중층)이 삭제되었습니다.');
      return;
    }
    separateMoleculeBonds(mol);
    const idx = state.molecules.indexOf(mol);
    if (idx !== -1) {
      state.molecules.splice(idx, 1);
      showHint(`[${mol.name}] 개체가 삭제되었습니다.`);
    }
  }

  function clearAll() {
    stopAutoPlay();
    state.molecules = [];
    state.bonds = [];
    state.history = [];
    state.waterParticles = [];
    state.slides = [];
    state.recentSplits = [];
    state.currentPreset = null;
    // 판서 내용도 함께 지움
    state.strokes = [];
    state.laserStrokes = [];
    state.currentStroke = null;
    renderDrawCanvas();
    showHint('화면이 모두 초기화되었습니다(판서 포함). 원하는 분자를 추가해보세요.');
  }

  // --------------------------------------------------------------------------
  // 9. 단계별 진행
  // --------------------------------------------------------------------------
  function nextStep() {
    const plan = findNextPlan();
    if (!plan) {
      showHint('✅ 더 이상 형성할 수 있는 결합이 없습니다.');
      return false;
    }
    formBond(plan);
    return true;
  }

  // 이전 단계: 마지막으로 한 일(분자 추가 또는 결합)을 거꾸로 되돌림
  function prevStep() {
    stopAutoPlay();
    while (state.history.length) {
      const h = state.history.pop();
      if (h.type === 'bond') {
        if (state.bonds.includes(h.bond) && !h.bond.hydrolyzing) { separateBond(h.bond); return; }
      } else if (h.type === 'add') {
        const alive = h.mols.filter(m => state.molecules.includes(m));
        if (alive.length) { undoAdd(alive); return; }
      }
      // 이미 다른 방법(더블클릭·결합 분리·삭제)으로 없어진 기록은 건너뜀
    }
    // 기록에 없는 결합이 남아 있으면 마지막 결합을 가수분해
    const last = state.bonds.filter(b => !b.hydrolyzing).pop();
    if (last) { separateBond(last); return; }
    showHint('되돌릴 단계가 없습니다.');
  }

  // 분자 추가 되돌리기: 추가했던 분자를 화면에서 제거
  function undoAdd(mols) {
    const set = new Set(mols);
    const related = state.bonds.filter(b => set.has(b.mol1) || set.has(b.mol2));
    if (related.length) {
      state.bonds = state.bonds.filter(b => !related.includes(b));
      state.waterParticles = state.waterParticles.filter(p => !related.includes(p.bond));
    }
    state.molecules = state.molecules.filter(m => !set.has(m));
    recalculateGroups();
    const isMembrane = mols[0].subType === 'pl_unit';
    showHint(`↩️ 이전 단계: [${isMembrane ? '세포막' : mols[0].name}] 추가를 취소했습니다.`);
  }

  function startAutoPlay() {
    if (!findNextPlan()) {
      showHint('✅ 더 이상 형성할 수 있는 결합이 없습니다.');
      return;
    }
    state.autoPlaying = true;
    nextStep();
    state.autoTimer = setInterval(() => {
      if (!nextStep()) stopAutoPlay();
    }, state.AUTO_INTERVAL);
    updatePlayButtons();
  }

  function stopAutoPlay() {
    if (state.autoTimer) clearInterval(state.autoTimer);
    state.autoTimer = null;
    state.autoPlaying = false;
    updatePlayButtons();
  }

  function toggleAutoPlay() {
    if (state.autoPlaying) stopAutoPlay();
    else startAutoPlay();
  }

  function updatePlayButtons() {
    dom.stepPlayBtn.textContent = state.autoPlaying ? '⏸ 정지' : '▶ 재생';
    dom.miniPlayBtn.textContent = state.autoPlaying ? '⏸' : '▶';
  }

  // 지금 화면에 불러온 프리셋 버튼만 색으로 표시 (분자를 직접 추가하거나 비우면 해제)
  function updatePresetButtons() {
    if (state.currentPreset === state.lastPresetShown) return;
    state.lastPresetShown = state.currentPreset;
    document.querySelectorAll('.preset-btn').forEach(btn => {
      btn.classList.toggle('active', btn.dataset.preset === state.currentPreset);
    });
  }

  function updateStepStatus() {
    const n = state.bonds.length;
    // '다음 결합 가능' 여부는 분자 위치가 아니라 분자·결합 구성에만 달려 있으므로,
    // 구성이 바뀐 경우에만 다시 계산 (매 프레임 모든 분자 쌍을 검사하지 않도록)
    const key = `${state.activeCategory}|${state.molecules.length}|${n}|` +
      state.bonds.map(b => b.id).join(',') + '|' + (state.molecules.length ? state.molecules[state.molecules.length - 1].id : '');
    if (key !== state.stepCache.key) {
      state.stepCache = { key, more: !!findNextPlan() };
    }
    const more = state.stepCache.more;
    const text = `결합 ${n}개 · ${more ? '다음 결합 가능' : '추가 결합 없음'}`;
    if (text === state.lastStepText) return;
    state.lastStepText = text;
    dom.stepStatus.textContent = `결합 ${n}개`;
    dom.stepStatus.title = text;
    dom.miniStepText.textContent = `결합 ${n}개`;
  }

  // --------------------------------------------------------------------------
  // 10. 프리셋
  // --------------------------------------------------------------------------
  const PRESET_CATEGORY = {
    maltose: 'carbs', sucrose: 'carbs', lactose: 'carbs', starch: 'carbs', cellulose: 'carbs',
    dipeptide: 'protein', tripeptide: 'protein', polypeptide: 'protein',
    triglyceride: 'lipid', phospholipid: 'lipid', bilayer: 'lipid'
  };

  function loadPreset(presetName) {
    // 프리셋이 속한 카테고리 화면으로 먼저 전환 (다른 카테고리 작업은 저장됨)
    if (PRESET_CATEGORY[presetName]) setCategory(PRESET_CATEGORY[presetName]);
    stopAutoPlay();
    state.molecules = [];
    state.bonds = [];
    state.waterParticles = [];
    state.slides = [];
    state.recentSplits = [];
    state.currentPreset = presetName;
    state.history = [];

    const push = (...ms) => state.molecules.push(...ms);
    const CHAIN_GAP = 290;       // 탄수화물 사슬: 결합 전 간격 (결합 후 180)
    const AMINO_GAP = 220;       // 단백질 사슬: 결합 전 간격 (결합 후 150, 판정 거리 밖이라 저절로 붙지 않음)

    switch (presetName) {
      case 'maltose':
        push(makeCarb('glucose', -150, 0), makeCarb('glucose', 150, 0));
        showHint('💡 엿당: 왼쪽 포도당의 1번 C(α)와 오른쪽 포도당의 4번 C가 α-1,4 결합합니다. 가까이 드래그해보세요.');
        break;

      case 'sucrose':
        push(makeCarb('glucose', -150, 0), makeCarb('fructose', 150, 0));
        showHint('💡 설탕: 포도당의 1번 C(α)와 과당의 2번 C(β)가 결합합니다.');
        break;

      case 'lactose':
        push(makeCarb('galactose', -150, 0), makeCarb('glucose', 150, 0));
        showHint('💡 젖당: 갈락토스의 1번 C(β)와 포도당의 4번 C가 β-1,4 결합합니다.');
        break;

      case 'starch': {
        const n = 4, start = -((n - 1) * CHAIN_GAP) / 2;
        for (let i = 0; i < n; i++) push(makeCarb('glucose', start + i * CHAIN_GAP, 0, { name: `α-포도당 #${i + 1}` }));
        showHint('💡 녹말: α-포도당 4개가 준비되었습니다. ▶ 재생 / 다음 ▶을 누르거나 맞닿게 드래그하면 α-1,4 결합합니다.');
        break;
      }

      case 'cellulose': {
        const n = 4, start = -((n - 1) * CHAIN_GAP) / 2;
        for (let i = 0; i < n; i++) {
          push(makeCarb('glucose', start + i * CHAIN_GAP, 0, {
            anomer: 'beta',
            flipped: i % 2 === 1,
            name: i % 2 === 1 ? 'β-포도당 (뒤집힘)' : 'β-포도당'
          }));
        }
        showHint('💡 셀룰로오스: β-포도당이 하나씩 뒤집혀 있습니다. ▶ 재생 / 다음 ▶을 누르거나 맞닿게 드래그하면 β-1,4 결합합니다.');
        break;
      }

      case 'dipeptide':
        push(makeAmino(AMINO_ACIDS[0], -150, 0), makeAmino(AMINO_ACIDS[1], 150, 0));
        showHint('💡 왼쪽 아미노산의 -COOH와 오른쪽 아미노산의 -NH₂가 만나 펩타이드 결합을 만듭니다.');
        break;

      case 'tripeptide':
        push(
          makeAmino(AMINO_ACIDS[0], -AMINO_GAP, 0),
          makeAmino(AMINO_ACIDS[9], 0, 0),
          makeAmino(AMINO_ACIDS[2], AMINO_GAP, 0)
        );
        showHint('💡 아미노산 3개 → 펩타이드 결합 2개, 물 분자 2개가 방출됩니다.');
        break;

      case 'polypeptide': {
        const chain = [AMINO_ACIDS[0], AMINO_ACIDS[1], AMINO_ACIDS[2], AMINO_ACIDS[9], AMINO_ACIDS[15]];
        const start = -((chain.length - 1) * AMINO_GAP) / 2;
        chain.forEach((aa, i) => push(makeAmino(aa, start + i * AMINO_GAP, 0)));
        showHint('💡 폴리펩타이드: 아미노산 5개가 준비되었습니다. ▶ 재생 / 다음 ▶을 누르거나 맞닿게 드래그하면 펩타이드 결합합니다.');
        break;
      }

      case 'triglyceride':
        push(
          makeLipidPart('glycerol', -180, 0),
          makeLipidPart('fatty_sat', 160, -75, '포화 지방산 1'),
          makeLipidPart('fatty_sat', 160, 0, '포화 지방산 2'),
          makeLipidPart('fatty_unsat', 160, 75, '불포화 지방산 3')
        );
        showHint('💡 글리세롤의 OH 3개에 지방산이 하나씩 에스터 결합 → 물 분자 3개 방출');
        break;

      case 'phospholipid':
        push(
          makeLipidPart('glycerol', -180, 0),
          makeLipidPart('fatty_sat', 175, -75, '포화 지방산 꼬리'),
          makeLipidPart('fatty_unsat', 175, 0, '불포화 지방산 꼬리'),
          makeLipidPart('phosphate', 180, 130, '인산기 (머리)')
        );
        showHint('💡 인지질: 글리세롤 1·2번 C에 지방산 2개, 3번 C에 인산기가 결합합니다.');
        break;

      case 'bilayer': {
        // 머리 사이·두 층 사이에 약간의 틈을 두고, 옆으로 길게 배열
        const n = PL_UNIT.COUNT, gap = PL_UNIT.HEAD_R * 2 + PL_UNIT.HEAD_GAP, len = PL_UNIT.LEN;
        const cy = len / 2 + PL_UNIT.LAYER_GAP / 2;  // 각 층 중심 (꼬리 끝 사이 LAYER_GAP만큼 떨어짐)
        const start = -((n - 1) * gap) / 2;
        // 자유 모드의 세포막과 같이 한 덩어리로 묶음 (드래그·삭제 시 통째로)
        const groupId = 'mem_' + Math.random().toString(36).slice(2, 9);
        for (let i = 0; i < n; i++) {
          push(
            new Molecule({ category: 'lipid', subType: 'pl_unit', name: '인지질(상)', x: start + i * gap, y: -cy, width: gap, height: len, data: { dir: 'down', fixedGroup: groupId } }),
            new Molecule({ category: 'lipid', subType: 'pl_unit', name: '인지질(하)', x: start + i * gap, y: cy, width: gap, height: len, data: { dir: 'up', fixedGroup: groupId } })
          );
        }
        state.molecules.forEach(m => { if (m.data.fixedGroup === groupId) m.groupId = groupId; });
        showHint('💡 친수성 머리는 바깥(물 쪽), 소수성 꼬리는 안쪽으로 모여 2중층을 이룹니다.');
        break;
      }
    }

    fitView();
  }

  // --------------------------------------------------------------------------
  // 11. 렌더 루프
  // --------------------------------------------------------------------------
  function renderLoop() {
    renderSimulation();
    // 레이저 필기가 사라지는 동안에만 판서 레이어를 매 프레임 다시 그림
    if (state.laserStrokes.length) renderDrawCanvas();
    updateStepStatus();
    updatePresetButtons();
    requestAnimationFrame(renderLoop);
  }

  function renderSimulation() {
    const isDark = state.theme === 'dark';
    simCtx.save();
    simCtx.setTransform(state.dpr, 0, 0, state.dpr, 0, 0);
    simCtx.fillStyle = isDark ? '#0b1120' : '#ffffff';
    simCtx.fillRect(0, 0, state.width, state.height);
    drawGrid(isDark ? '#1e293b' : '#f1f5f9');

    simCtx.translate(state.view.offsetX, state.view.offsetY);
    simCtx.scale(state.view.scale, state.view.scale);

    updateSlides();
    drawBonds(isDark);
    state.molecules.forEach(mol => drawMolecule(mol, isDark));
    updateAndDrawWater(isDark);

    simCtx.restore();
  }

  function drawGrid(gridColor) {
    simCtx.save();
    simCtx.strokeStyle = gridColor;
    simCtx.lineWidth = 1;
    const gridSize = 40 * state.view.scale;
    const sx = ((state.view.offsetX % gridSize) + gridSize) % gridSize;
    const sy = ((state.view.offsetY % gridSize) + gridSize) % gridSize;
    simCtx.beginPath();
    for (let x = sx; x < state.width; x += gridSize) { simCtx.moveTo(x, 0); simCtx.lineTo(x, state.height); }
    for (let y = sy; y < state.height; y += gridSize) { simCtx.moveTo(0, y); simCtx.lineTo(state.width, y); }
    simCtx.stroke();
    simCtx.restore();
  }

  // --------------------------------------------------------------------------
  // 12. 공통 그리기 유틸
  // --------------------------------------------------------------------------
  function palette(isDark) {
    return {
      text: isDark ? '#f8fafc' : '#000000',
      line: isDark ? '#f8fafc' : '#000000',
      reactiveText: isDark ? '#f0fdf4' : '#065f46'
    };
  }

  function drawHighlightCircle(x, y, radius, isDark) {
    simCtx.save();
    simCtx.beginPath();
    simCtx.arc(x, y, radius, 0, Math.PI * 2);
    simCtx.fillStyle = isDark ? '#166534' : '#86efac';
    simCtx.fill();
    simCtx.strokeStyle = isDark ? '#4ade80' : '#22c55e';
    simCtx.lineWidth = 1.8;
    simCtx.stroke();
    simCtx.restore();
  }

  // 반응에 참여하는 작용기 (연두색 원 + 글자)
  function drawReactive(x, y, text, isDark, radius) {
    const c = palette(isDark);
    drawHighlightCircle(x, y, radius || (text.length > 1 ? 13 : 12), isDark);
    simCtx.fillStyle = c.reactiveText;
    simCtx.font = 'bold 13px sans-serif';
    simCtx.textAlign = 'center';
    simCtx.textBaseline = 'middle';
    simCtx.fillText(text, x, y);
  }

  function drawBondLine(x1, y1, x2, y2, color, width = 1.8) {
    simCtx.save();
    simCtx.lineWidth = width;
    simCtx.strokeStyle = color;
    simCtx.beginPath();
    simCtx.moveTo(x1, y1);
    simCtx.lineTo(x2, y2);
    simCtx.stroke();
    simCtx.restore();
  }

  function text(str, x, y, font, color) {
    simCtx.font = font;
    simCtx.fillStyle = color;
    simCtx.textAlign = 'center';
    simCtx.textBaseline = 'middle';
    simCtx.fillText(str, x, y);
  }

  // 글자의 실제 잉크 모양 기준으로 (x, y)에 정확히 가운데 맞춤 (원 안의 원소 기호 등)
  function textInkCentered(str, x, y, font, color) {
    simCtx.save();
    simCtx.font = font;
    simCtx.fillStyle = color;
    simCtx.textAlign = 'left';
    simCtx.textBaseline = 'alphabetic';
    const m = simCtx.measureText(str);
    if (m.actualBoundingBoxAscent === undefined) {
      // 측정 정보를 지원하지 않는 환경: 기존 방식
      simCtx.textAlign = 'center';
      simCtx.textBaseline = 'middle';
      simCtx.fillText(str, x, y);
    } else {
      const inkW = m.actualBoundingBoxLeft + m.actualBoundingBoxRight;
      const drawX = x - inkW / 2 + m.actualBoundingBoxLeft;
      const drawY = y + (m.actualBoundingBoxAscent - m.actualBoundingBoxDescent) / 2;
      simCtx.fillText(str, drawX, drawY);
    }
    simCtx.restore();
  }

  function roundRect(ctx, x, y, width, height, radius) {
    ctx.beginPath();
    ctx.moveTo(x + radius, y);
    ctx.lineTo(x + width - radius, y);
    ctx.quadraticCurveTo(x + width, y, x + width, y + radius);
    ctx.lineTo(x + width, y + height - radius);
    ctx.quadraticCurveTo(x + width, y + height, x + width - radius, y + height);
    ctx.lineTo(x + radius, y + height);
    ctx.quadraticCurveTo(x, y + height, x, y + height - radius);
    ctx.lineTo(x, y + radius);
    ctx.quadraticCurveTo(x, y, x + radius, y);
    ctx.closePath();
  }

  function polygon(cx, cy, r, sides, rotation) {
    simCtx.beginPath();
    for (let i = 0; i < sides; i++) {
      const a = rotation + (i * 2 * Math.PI) / sides;
      const px = cx + r * Math.cos(a), py = cy + r * Math.sin(a);
      if (i === 0) simCtx.moveTo(px, py); else simCtx.lineTo(px, py);
    }
    simCtx.closePath();
  }

  // --------------------------------------------------------------------------
  // 13. 분자 렌더러
  // --------------------------------------------------------------------------
  function drawMolecule(m, isDark) {
    simCtx.save();
    simCtx.translate(m.x, m.y);
    const simple = state.displayMode === 'simple';

    if (m.category === 'carbs') simple ? drawCarbSimple(m, isDark) : drawCarb(m, isDark);
    else if (m.category === 'protein') simple ? drawAminoSimple(m, isDark) : drawAminoAcid(m, isDark);
    else if (m.category === 'lipid') simple ? drawLipidSimple(m, isDark) : drawLipid(m, isDark);

    simCtx.restore();
  }

  function carbFill(m, isDark) {
    if (isDark) return '#334155';
    return { glucose: '#fef08a', galactose: '#d9f99d', fructose: '#fed7aa' }[m.subType];
  }

  // (A) 탄수화물 - 하워스 투영식
  function drawCarb(m, isDark) {
    if (m.subType === 'fructose') drawFructose(m, isDark);
    else drawPyranose(m, isDark);
    text(m.name, 0, 96, 'bold 17px sans-serif', palette(isDark).text);
  }

  // 수직 치환기 (dir: -1 위 / +1 아래, 상하 반전 반영)
  function makeSub(fy, c) {
    return (atom, dir, label, len = 18, gap = 28, bold = false) => {
      const d = dir * fy;
      drawBondLine(atom.x, atom.y, atom.x, atom.y + d * len, c.line);
      text(label, atom.x, atom.y + d * gap, (bold ? 'bold ' : '') + '15px sans-serif', c.text);
    };
  }

  function drawRingOutline(points, frontIdx, oIdx, fill, c) {
    const n = points.length;
    const ringPath = () => {
      simCtx.beginPath();
      points.forEach((p, i) => (i === 0 ? simCtx.moveTo(p.x, p.y) : simCtx.lineTo(p.x, p.y)));
      simCtx.closePath();
    };

    // 고리 채움
    ringPath();
    simCtx.fillStyle = fill;
    simCtx.fill();

    // 앞쪽 굵은 선: 고리 안쪽으로만 보이게 잘라서 바깥 테두리가 기본 선과 맞도록
    // (두께 11로 그리고 고리 모양으로 잘라내면 안쪽 5.5만 보임)
    simCtx.save();
    ringPath();
    simCtx.clip();
    simCtx.strokeStyle = c.line;
    simCtx.lineWidth = 11;
    simCtx.lineCap = 'butt';
    simCtx.lineJoin = 'miter';
    simCtx.beginPath();
    frontIdx.forEach((i, k) => {
      const a = points[i], b = points[(i + 1) % n];
      if (k === 0 || frontIdx[k - 1] !== i - 1) simCtx.moveTo(a.x, a.y);
      simCtx.lineTo(b.x, b.y);
    });
    simCtx.stroke();
    simCtx.restore();

    // 뒤쪽 얇은 선
    simCtx.strokeStyle = c.line;
    simCtx.lineCap = 'round';
    simCtx.lineWidth = 2.2;
    for (let i = 0; i < n; i++) {
      if (frontIdx.includes(i)) continue;
      const a = points[i], b = points[(i + 1) % n];
      let ax = a.x, ay = a.y, bx = b.x, by = b.y;
      // 고리 산소(O) 글자 주변은 선을 비움
      const shrink = (px, py, qx, qy) => {
        const len = Math.hypot(qx - px, qy - py);
        return { x: px + ((qx - px) / len) * 10, y: py + ((qy - py) / len) * 10 };
      };
      if (i === oIdx) { const s = shrink(ax, ay, bx, by); ax = s.x; ay = s.y; }
      if ((i + 1) % n === oIdx) { const s = shrink(bx, by, ax, ay); bx = s.x; by = s.y; }
      simCtx.beginPath();
      simCtx.moveTo(ax, ay);
      simCtx.lineTo(bx, by);
      simCtx.stroke();
    }
  }

  // C·H 표시: 고리 꼭짓점의 생략된 탄소를 'C'로 표시 (선이 글자를 가리지 않도록 바탕 원)
  function drawRingCarbons(atoms, isDark) {
    if (!state.showCH) return;
    const c = palette(isDark);
    atoms.forEach(a => {
      simCtx.beginPath();
      simCtx.arc(a.x, a.y, 8.5, 0, Math.PI * 2);
      simCtx.fillStyle = isDark ? '#0b1120' : '#ffffff';
      simCtx.fill();
      textInkCentered('C', a.x, a.y, 'bold 14px sans-serif', c.text);
    });
  }

  // 지방산 이름: 사슬 오른쪽 끝 옆에 왼쪽 정렬로 표시 (분자 위가 복잡해지지 않도록)
  function drawFattyName(isSat, x, y, c) {
    simCtx.save();
    simCtx.font = 'bold 13px sans-serif';
    simCtx.fillStyle = c.text;
    simCtx.textAlign = 'left';
    simCtx.textBaseline = 'middle';
    simCtx.globalAlpha = 0.75;
    simCtx.fillText(isSat ? '포화 지방산' : '불포화 지방산', x, y);
    simCtx.restore();
  }

  // C·H 표시: 지방산 탄소 사슬을 C와 H로 펼쳐 그림
  //  - 포화: CH₂ … CH₃ (모두 단일결합)
  //  - 불포화: 가운데 C=C 이중결합(시스형: 두 H가 같은 쪽) 뒤로 사슬이 꺾임
  function drawExplicitFattyChain(c, isSat) {
    const atoms = isSat
      ? [
          { x: -26, y: 0, up: 1, down: 1 },
          { x: -4, y: 0, up: 1, down: 1 },
          { x: 18, y: 0, up: 1, down: 1 },
          { x: 40, y: 0, up: 1, down: 1 },
          { x: 62, y: 0, up: 1, down: 1 },
          { x: 84, y: 0, up: 1, down: 1, right: 1 }
        ]
      : [
          { x: -26, y: 0, up: 1, down: 1 },
          { x: -4, y: 0, up: 1, down: 1 },
          { x: 18, y: 0, up: 1 },             // 이중결합 탄소 (H 1개)
          { x: 40, y: 0, up: 1 },             // 이중결합 탄소 (H 1개, 같은 쪽 → 시스)
          { x: 58, y: 12, up: 1, down: 1 },
          { x: 78, y: 16, up: 1, down: 1, right: 1 }
        ];
    const bonds = atoms.slice(1).map((_, i) => ({ a: i, b: i + 1, order: (!isSat && i === 2) ? 2 : 1 }));
    const font = 'bold 13px sans-serif', hFont = '12px sans-serif';
    const GAP = 7; // 결합선이 C 글자를 가리지 않도록 양 끝을 비움

    const bondLine = (p, q, order) => {
      const dx = q.x - p.x, dy = q.y - p.y, len = Math.hypot(dx, dy) || 1;
      const ux = dx / len, uy = dy / len;
      const x1 = p.x + ux * GAP, y1 = p.y + uy * GAP, x2 = q.x - ux * GAP, y2 = q.y - uy * GAP;
      if (order === 2) {
        const nx = -uy * 2.6, ny = ux * 2.6;
        drawBondLine(x1 + nx, y1 + ny, x2 + nx, y2 + ny, c.line);
        drawBondLine(x1 - nx, y1 - ny, x2 - nx, y2 - ny, c.line);
      } else {
        drawBondLine(x1, y1, x2, y2, c.line);
      }
    };

    bondLine({ x: -56, y: 0 }, atoms[0], 1);  // 카복실기 C와 연결
    bonds.forEach(b => bondLine(atoms[b.a], atoms[b.b], b.order));
    atoms.forEach(a => {
      text('C', a.x, a.y, font, c.text);
      if (a.up) { drawBondLine(a.x, a.y - 8, a.x, a.y - 15, c.line); text('H', a.x, a.y - 22, hFont, c.text); }
      if (a.down) { drawBondLine(a.x, a.y + 8, a.x, a.y + 15, c.line); text('H', a.x, a.y + 22, hFont, c.text); }
      if (a.right) { drawBondLine(a.x + 7, a.y, a.x + 14, a.y, c.line); text('H', a.x + 20, a.y, hFont, c.text); }
    });
  }

  // 포도당·갈락토스 (6각 고리, 1번 C 오른쪽 / 4번 C 왼쪽)
  function drawPyranose(m, isDark) {
    const c = palette(isDark);
    const fy = flipY(m);
    const P = (x, y) => ({ x, y: y * fy });
    // 좌우 대칭 육각형: 위 변(C5–O)과 아래 변(C3–C2) 길이 동일 (64px)
    const C5 = P(-32, -30), O = P(32, -30), C1 = P(62, 6), C2 = P(32, 42), C3 = P(-32, 42), C4 = P(-62, 6);
    const isGal = m.subType === 'galactose';
    const sub = makeSub(fy, c);

    // 점 순서: C5, O, C1, C2, C3, C4 → 앞쪽(굵은 선) 변: C1-C2, C2-C3, C3-C4
    drawRingOutline([C5, O, C1, C2, C3, C4], [2, 3, 4], 1, carbFill(m, isDark), c);
    text('O', O.x, O.y, 'bold 18px sans-serif', c.text);

    // C5: 위 CH₂OH, 아래 H
    sub(C5, -1, 'CH₂OH', 20, 30, true);
    sub(C5, +1, 'H', 12, 22);   // 고리 안쪽은 짧게 (C3의 OH와 겹치지 않도록)
    // C3: 위 OH, 아래 H
    sub(C3, -1, 'OH', 12, 22);
    sub(C3, +1, 'H');
    // C2: 위 H, 아래 OH
    sub(C2, -1, 'H', 12, 22);
    sub(C2, +1, 'OH');

    // C4: 포도당은 OH 아래, 갈락토스는 OH 위 (4번 탄소 에피머)
    const c4Dir = isGal ? -1 : +1;
    sub(C4, -c4Dir, 'H');
    if (!m.isLeftBonded()) {
      const d = c4Dir * fy;
      drawBondLine(C4.x, C4.y, C4.x - 14, C4.y + d * 14, c.line);
      drawReactive(C4.x - 24, C4.y + d * 22, 'HO', isDark);
    }

    // C1: α는 OH 아래, β는 OH 위
    const r = m.data.anomer === 'beta' ? -1 : +1;
    sub(C1, -r, 'H');
    if (!m.isRightBonded()) {
      const d = r * fy;
      drawBondLine(C1.x, C1.y, C1.x + 14, C1.y + d * 14, c.line);
      const oy = C1.y + d * 22;
      text('O', C1.x + 22, oy, '15px sans-serif', c.text);
      // O—H 사이를 짧은 선으로 연결 (H 원이 O 글자를 가리지 않도록 오른쪽으로 띄움)
      drawBondLine(C1.x + 29, oy, C1.x + 39, oy, c.line);
      drawReactive(C1.x + 51, oy, 'H', isDark);
    }

    // 고리 안쪽 α/β 표시
    text(m.data.anomer === 'beta' ? 'β' : 'α', 0, 6 * fy, 'bold 14px sans-serif', isDark ? '#94a3b8' : '#92400e');
    drawRingCarbons([C1, C2, C3, C4, C5], isDark);
  }

  // 과당 (5각 고리, 2번 C가 왼쪽 → 포도당 1번 C와 결합)
  function drawFructose(m, isDark) {
    const c = palette(isDark);
    const fy = flipY(m);
    const P = (x, y) => ({ x, y: y * fy });
    const O = P(0, -30), C2 = P(-42, -6), C3 = P(-26, 34), C4 = P(26, 34), C5 = P(42, -6);
    const sub = makeSub(fy, c);

    // 점 순서: O, C5, C4, C3, C2 → 앞쪽 변: C5-C4, C4-C3, C3-C2
    drawRingOutline([O, C5, C4, C3, C2], [1, 2, 3], 0, carbFill(m, isDark), c);
    text('O', O.x, O.y, 'bold 17px sans-serif', c.text);

    // C2: 위 CH₂OH(1번 C), 아래 반응 OH
    sub(C2, -1, 'CH₂OH', 18, 26, true);
    if (!m.isLeftBonded()) {
      drawBondLine(C2.x, C2.y, C2.x - 14, C2.y + 14 * fy, c.line);
      drawReactive(C2.x - 24, C2.y + 22 * fy, 'HO', isDark);
    }
    // C3: 위 OH, 아래 H
    sub(C3, -1, 'OH', 18, 28);
    sub(C3, +1, 'H', 18, 26);
    // C4: 위 H, 아래 OH
    sub(C4, -1, 'H', 18, 26);
    sub(C4, +1, 'OH', 18, 28);
    // C5: 위 H, 아래 CH₂OH(6번 C)
    sub(C5, -1, 'H', 18, 26);
    drawBondLine(C5.x, C5.y, C5.x + 12, C5.y + 14 * fy, c.line);
    text('CH₂OH', C5.x + 32, C5.y + 24 * fy, 'bold 14px sans-serif', c.text);

    text('β', 0, 8 * fy, 'bold 14px sans-serif', isDark ? '#94a3b8' : '#9a3412');
    drawRingCarbons([C2, C3, C4, C5], isDark);
  }

  // 탄수화물 간편 모형
  function drawCarbSimple(m, isDark) {
    const c = palette(isDark);
    const isFru = m.subType === 'fructose';
    polygon(0, 0, 48, isFru ? 5 : 6, isFru ? -Math.PI / 2 : 0);
    simCtx.fillStyle = carbFill(m, isDark);
    simCtx.fill();
    simCtx.lineWidth = 3;
    simCtx.strokeStyle = c.line;
    simCtx.stroke();

    text(m.name.replace(/\s*\(.*\)/, ''), 0, -4, 'bold 15px sans-serif', c.text);
    if (!isFru) text(m.data.anomer === 'beta' ? 'β' : 'α', 0, 16, 'bold 13px sans-serif', isDark ? '#94a3b8' : '#92400e');
    if (m.data.flipped) text('(뒤집힘)', 0, 70, '13px sans-serif', isDark ? '#94a3b8' : '#64748b');

    if (!m.isLeftBonded()) drawReactive(-62, 0, 'OH', isDark);
    if (!isFru && !m.isRightBonded()) drawReactive(62, 0, 'H', isDark);
  }

  // (B) 아미노산 구조식
  function drawAminoAcid(m, isDark) {
    const aa = m.data || AMINO_ACIDS[0];
    const c = palette(isDark);

    // 중심 Cα와 H
    text('C', 0, 0, 'bold 16px sans-serif', c.text);
    drawBondLine(0, -10, 0, -28, c.line);
    text('H', 0, -38, 'bold 16px sans-serif', c.text);

    // R기 (글자 길이에 맞춰 상자 폭 조정)
    drawBondLine(0, 10, 0, 26, c.line);
    simCtx.font = 'bold 11.5px sans-serif';
    const rText = `R: ${aa.rGroup}`;
    const boxW = Math.max(88, simCtx.measureText(rText).width + 16);
    roundRect(simCtx, -boxW / 2, 30, boxW, 30, 8);
    simCtx.fillStyle = isDark ? '#1e293b' : '#fef3c7';
    simCtx.fill();
    simCtx.lineWidth = 1.5;
    simCtx.strokeStyle = '#f59e0b';
    simCtx.stroke();
    text(rText, 0, 45, 'bold 11.5px sans-serif', isDark ? '#fbbf24' : '#b45309');

    // 왼쪽 아미노기
    drawBondLine(-10, 0, -32, 0, c.line);
    const nColor = isDark ? '#60a5fa' : '#2563eb';
    text('N', -42, 0, 'bold 16px sans-serif', nColor);
    if (aa.code === 'Pro') {
      // 프롤린: N이 R기와 고리를 이룸(2차 아민) → 위쪽 H 대신 R기로 이어지는 선
      // 펩타이드 결합 후에는 N에 H가 남지 않음
      drawBondLine(-42, 9, -42, 30, c.line);
    } else {
      // 아미노기 N과 위쪽 H (펩타이드 결합 후에도 N–H는 남음: -CO-NH-)
      drawBondLine(-42, -9, -42, -22, c.line);
      text('H', -42, -31, 'bold 15px sans-serif', nColor);
    }
    if (!m.isLeftBonded()) {
      // 결합 전: 반응에 참여하는 왼쪽 H를 N과 선으로 연결 (H—N)
      drawBondLine(-51, 0, -61, 0, c.line);
      drawReactive(-72, 0, 'H', isDark, 11);
    }

    // 오른쪽 카복실기 C=O
    drawBondLine(10, 0, 32, 0, c.line);
    text('C', 42, 0, 'bold 16px sans-serif', c.text);
    // C=O 이중선: C·O 글자와 닿지 않도록 위아래 틈을 둠
    drawBondLine(40, -12, 40, -23, c.line, 2);
    drawBondLine(45, -12, 45, -23, c.line, 2);
    text('O', 42, -35, 'bold 16px sans-serif', '#ef4444');

    if (!m.isRightBonded()) {
      drawBondLine(50, 0, 66, 0, c.line);
      drawReactive(79, 0, 'OH', isDark);
    }

    text(`${aa.name} (${aa.code})`, 0, 78, 'bold 16px sans-serif', c.text);
  }

  // 아미노산 간편 모형
  function drawAminoSimple(m, isDark) {
    const aa = m.data || AMINO_ACIDS[0];
    const c = palette(isDark);
    simCtx.beginPath();
    simCtx.arc(0, 0, 40, 0, Math.PI * 2);
    simCtx.fillStyle = isDark ? '#334155' : AA_SIMPLE_COLORS[aa.type];
    simCtx.fill();
    simCtx.lineWidth = 3;
    simCtx.strokeStyle = c.line;
    simCtx.stroke();
    text(aa.code, 0, -7, 'bold 19px sans-serif', c.text);
    text(aa.name, 0, 14, 'bold 12px sans-serif', c.text);

    if (!m.isLeftBonded()) drawReactive(-54, 0, 'H', isDark);
    if (!m.isRightBonded()) drawReactive(56, 0, 'OH', isDark);
  }

  // (C) 지질 구조식
  function glycerolSlotBound(m, slot) {
    return state.bonds.some(b => b.mol1 === m && b.slot === slot);
  }

  function glycerolSlotPhosphate(m, slot) {
    return state.bonds.some(b => b.mol1 === m && b.slot === slot && b.mol2.subType === 'phosphate');
  }

  function drawLipid(m, isDark) {
    const c = palette(isDark);

    if (m.subType === 'glycerol') {
      // 탄소 사슬 세로선: C 글자를 가리지 않도록 탄소 사이 구간만 그림
      const cX = -14;
      drawBondLine(cX, -75 + 12, cX, 0 - 12, c.line, 2.5);
      drawBondLine(cX, 0 + 12, cX, 75 - 12, c.line, 2.5);
      [-75, 0, 75].forEach((cy, i) => {
        text('C', cX, cy, 'bold 16px sans-serif', c.text);
        const withP = glycerolSlotPhosphate(m, cy);
        if (withP) {
          // 인산기가 붙은 탄소: 왼쪽은 O(—P), 오른쪽은 H  →  P—O—C—H
          drawBondLine(cX - 10, cy, cX - 24, cy, c.line);
          text('O', cX - 32, cy, 'bold 16px sans-serif', '#ef4444');
        } else {
          // 왼쪽 H를 선으로 연결 (H—C)
          drawBondLine(cX - 10, cy, cX - 24, cy, c.line);
          text('H', cX - 32, cy, 'bold 16px sans-serif', c.text);
        }
        if (i !== 1) {
          // 양 끝 탄소는 H가 하나 더: 맨 위는 위쪽, 맨 아래는 아래쪽으로 선 연결
          const d = i === 0 ? -1 : 1;
          drawBondLine(cX, cy + d * 11, cX, cy + d * 24, c.line);
          text('H', cX, cy + d * 33, 'bold 16px sans-serif', c.text);
        }
        drawBondLine(cX + 10, cy, 24, cy, c.line);
        if (withP) {
          text('H', 31, cy, 'bold 16px sans-serif', c.text);
        } else if (glycerolSlotBound(m, cy)) {
          // 에스터 결합 후에도 글리세롤의 O는 남음 (-COO-)
          text('O', 31, cy, 'bold 16px sans-serif', '#ef4444');
        } else {
          drawReactive(37, cy, 'OH', isDark);
        }
      });
      text('글리세롤', 0, 150, 'bold 16px sans-serif', c.text);
    } else if (m.subType === 'fatty_sat' || m.subType === 'fatty_unsat') {
      const isSat = m.subType === 'fatty_sat';
      if (!m.isLeftBonded()) {
        drawReactive(-90, 0, 'HO', isDark);
        drawBondLine(-77, 0, -64, 0, c.line);
      }
      text('C', -56, 0, 'bold 15px sans-serif', c.text);
      // C=O 이중선: C·O 글자와 닿지 않도록 위아래 틈을 둠
      drawBondLine(-58, -11, -58, -22, c.line);
      drawBondLine(-53, -11, -53, -22, c.line);
      text('O', -56, -33, 'bold 15px sans-serif', '#ef4444');
      if (state.showCH) {
        drawExplicitFattyChain(c, isSat);
        drawFattyName(isSat, isSat ? 112 : 106, isSat ? 0 : 16, c);
      } else {
        drawBondLine(-48, 0, -32, 0, c.line);
        drawFattyTail(isSat, -32);
        text('CH₃', 96, isSat ? 0 : 20, 'bold 14px sans-serif', c.text);
        drawFattyName(isSat, 116, isSat ? 0 : 20, c);
      }
    } else if (m.subType === 'phosphate') {
      drawPhosphate(m, isDark);
    } else if (m.subType === 'pl_unit') {
      drawPhospholipidUnit(m, c);
    }
  }

  // 인산기: 큰 원 (친수성 머리) + 왼쪽에 반응하는 HO
  function drawPhosphate(m, isDark) {
    const c = palette(isDark);
    const r = state.PHOSPHATE_R;
    if (!m.isLeftBonded()) {
      drawBondLine(-r - 11, 0, -r - 1, 0, c.line);
      drawReactive(-r - 24, 0, 'HO', isDark);
    }
    simCtx.beginPath();
    simCtx.arc(0, 0, r, 0, Math.PI * 2);
    simCtx.fillStyle = '#e11d48';
    simCtx.fill();
    simCtx.lineWidth = 3;
    simCtx.strokeStyle = c.line;
    simCtx.stroke();
    text('P', 0, -6, 'bold 22px sans-serif', '#ffffff');
    text('인산기', 0, 14, 'bold 11px sans-serif', '#ffffff');
  }

  function drawFattyTail(isSat, startX) {
    simCtx.save();
    simCtx.lineWidth = 3;
    simCtx.strokeStyle = isSat ? '#4f46e5' : '#ec4899';
    simCtx.lineJoin = 'round';
    simCtx.beginPath();
    if (isSat) {
      let toggle = true;
      for (let x = startX; x <= 80; x += 14) {
        const y = toggle ? -7 : 7;
        if (x === startX) simCtx.moveTo(x, y); else simCtx.lineTo(x, y);
        toggle = !toggle;
      }
    } else {
      simCtx.moveTo(startX, 0);
      simCtx.lineTo(-4, -6);
      simCtx.lineTo(12, 18);
      simCtx.lineTo(40, 24);
      simCtx.lineTo(75, 20);
    }
    simCtx.stroke();
    simCtx.restore();
  }

  // 2중층 인지질 한 개: 친수성 머리(원) + 긴 소수성 꼬리 2개 (오른쪽 꼬리는 불포화로 꺾임)
  function drawPhospholipidUnit(m, c) {
    const dir = m.data.dir === 'down' ? 1 : -1;   // 1: 머리 위·꼬리 아래 / -1: 반대
    const r = PL_UNIT.HEAD_R, half = PL_UNIT.LEN / 2;
    const headY = -dir * (half - r);
    const t0 = headY + dir * (r - 2);              // 꼬리 시작 (머리 가장자리)
    const t1 = dir * (half - 1);                   // 꼬리 끝 (반대층 꼬리와 맞닿는 곳)
    const at = (p) => t0 + (t1 - t0) * p;

    simCtx.save();
    simCtx.strokeStyle = '#f59e0b';
    simCtx.lineWidth = 4;
    simCtx.lineCap = 'round';
    simCtx.lineJoin = 'round';
    simCtx.beginPath();
    simCtx.moveTo(-7, t0);
    simCtx.lineTo(-7, t1);
    simCtx.moveTo(7, t0);
    simCtx.lineTo(7, at(0.45));
    simCtx.lineTo(15, at(0.6));
    simCtx.lineTo(15, t1);
    simCtx.stroke();
    simCtx.restore();

    simCtx.beginPath();
    simCtx.arc(0, headY, r, 0, Math.PI * 2);
    simCtx.fillStyle = '#0284c7';
    simCtx.fill();
    simCtx.lineWidth = 2.5;
    simCtx.strokeStyle = c.text;
    simCtx.stroke();
  }

  // 지질 간편 모형
  function drawLipidSimple(m, isDark) {
    const c = palette(isDark);
    if (m.subType === 'glycerol') {
      roundRect(simCtx, -30, -100, 60, 200, 14);
      simCtx.fillStyle = isDark ? '#334155' : '#fde68a';
      simCtx.fill();
      simCtx.lineWidth = 3;
      simCtx.strokeStyle = c.line;
      simCtx.stroke();
      text('글리', 0, -12, 'bold 15px sans-serif', c.text);
      text('세롤', 0, 8, 'bold 15px sans-serif', c.text);
      [-75, 0, 75].forEach(slot => {
        if (!glycerolSlotBound(m, slot)) drawReactive(44, slot, 'OH', isDark);
      });
    } else if (m.subType === 'fatty_sat' || m.subType === 'fatty_unsat') {
      const isSat = m.subType === 'fatty_sat';
      simCtx.save();
      simCtx.lineWidth = 8;
      simCtx.lineCap = 'round';
      simCtx.strokeStyle = isSat ? '#4f46e5' : '#ec4899';
      simCtx.beginPath();
      simCtx.moveTo(-78, 0);
      if (isSat) simCtx.lineTo(95, 0);
      else { simCtx.lineTo(10, 0); simCtx.lineTo(90, 22); }
      simCtx.stroke();
      simCtx.restore();
      drawFattyName(isSat, isSat ? 106 : 100, isSat ? 0 : 22, c);
      if (!m.isLeftBonded()) drawReactive(-98, 0, 'HO', isDark);
    } else if (m.subType === 'phosphate') {
      drawPhosphate(m, isDark);
    } else if (m.subType === 'pl_unit') {
      drawPhospholipidUnit(m, c);
    }
  }

  // --------------------------------------------------------------------------
  // 14. 결합 브릿지 기하 & 렌더러
  // --------------------------------------------------------------------------
  // 결합 위치 계산 (표시 모드별) → { p1, p2, o(브릿지 중심), tagX, tagY }
  function bondGeometry(bond) {
    const m1 = bond.mol1, m2 = bond.mol2;
    const simple = state.displayMode === 'simple';

    if (bond.type === 'glycosidic') {
      if (simple) {
        const p1 = { x: m1.x + 48, y: m1.y }, p2 = { x: m2.x - 48, y: m2.y };
        const o = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
        return { p1, p2, o, tagX: o.x, tagY: o.y + 66 };
      }
      const f1 = flipY(m1), f2 = flipY(m2);
      const p1 = { x: m1.x + 62, y: m1.y + 6 * f1 };
      const p2 = m2.subType === 'fructose'
        ? { x: m2.x - 42, y: m2.y - 6 * f2 }
        : { x: m2.x - 62, y: m2.y + 6 * f2 };
      const dir = c1Dir(m1);
      const baseY = (m1.y + m2.y) / 2;
      const o = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 + dir * 24 };
      let tagY;
      if (dir > 0) tagY = o.y + 34;           // 산소 다리가 아래 → 라벨도 아래
      else if (f2 === -1) tagY = o.y - 34;    // 위 다리 + 오른쪽이 뒤집힘 → 위쪽이 비어 있음
      else tagY = baseY + 66;                 // 위 다리 + 오른쪽 정상 → 아래쪽이 비어 있음
      return { p1, p2, o, tagX: o.x, tagY };
    }

    if (bond.type === 'peptide') {
      const p1 = { x: m1.x + (simple ? 40 : 50), y: m1.y };
      const p2 = { x: m2.x - (simple ? 40 : 52), y: m2.y };
      const o = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
      return { p1, p2, o, tagX: o.x, tagY: o.y + (simple ? 62 : -62) };
    }

    // ester
    const isP = m2.subType === 'phosphate';
    if (isP) {
      // 인산기: 글리세롤 왼쪽 O → 인산기 원 오른쪽 가장자리
      const p1 = { x: m1.x - (simple ? 30 : 54), y: m2.y };
      const p2 = { x: m2.x + state.PHOSPHATE_R + 1, y: m2.y };
      const o = { x: (p1.x + p2.x) / 2, y: m2.y };
      // 인산기 원과 겹치지 않도록 바깥쪽(맨 위 자리는 위, 맨 아래 자리는 아래)에 이름표
      const outward = m2.y < m1.y ? -1 : 1;
      return { p1, p2, o, tagX: o.x - 4, tagY: m2.y + outward * 48 };
    }
    const p1 = { x: m1.x + (simple ? 30 : 39), y: m2.y };
    const p2 = { x: m2.x - (simple ? 82 : 64), y: m2.y };
    const o = { x: (p1.x + p2.x) / 2, y: m2.y };
    if (simple) return { p1, p2, o, tagX: p1.x + 6, tagY: m2.y + 26, tagAlign: 'left' };
    // 구조식: 이름표를 결합선 왼쪽에 붙여, 아래 자리 지방산의 C=O(O 글자)와 닿지 않게 함
    return { p1, p2, o, tagX: m1.x + 12, tagY: m2.y + 25, tagAlign: 'left' };
  }

  function bondSite(bond) {
    return bondGeometry(bond).o;
  }

  function drawBonds(isDark) {
    const simple = state.displayMode === 'simple';
    const colors = { glycosidic: '#ef4444', peptide: '#2563eb', ester: '#7c3aed' };

    state.bonds.forEach(bond => {
      const g = bondGeometry(bond);
      const color = colors[bond.type];
      simCtx.save();
      simCtx.lineWidth = simple ? 6 : 4;
      // 가수분해 진행 중인 결합은 깜빡이며 표시
      if (bond.hydrolyzing) simCtx.globalAlpha = 0.45 + 0.35 * Math.sin(nowMs() / 120);
      simCtx.lineCap = 'round';
      simCtx.strokeStyle = color;

      if (bond.type === 'glycosidic') {
        // C1 → 다리 산소(O) → 상대 탄소, 글자 주변은 비움
        const seg = (a, b) => {
          const len = Math.hypot(b.x - a.x, b.y - a.y) || 1;
          const ex = b.x - ((b.x - a.x) / len) * 13;
          const ey = b.y - ((b.y - a.y) / len) * 13;
          simCtx.moveTo(a.x, a.y);
          simCtx.lineTo(ex, ey);
        };
        simCtx.beginPath();
        seg(g.p1, g.o);
        seg(g.p2, g.o);
        simCtx.stroke();
        text('O', g.o.x, g.o.y, 'bold 22px sans-serif', isDark ? '#ffffff' : '#000000');
      } else {
        simCtx.beginPath();
        simCtx.moveTo(g.p1.x, g.p1.y);
        simCtx.lineTo(g.p2.x, g.p2.y);
        simCtx.stroke();
      }
      simCtx.restore();

      if (state.showBondLabels) drawBondTag(g.tagX, g.tagY, bond.label, color, isDark, g.tagAlign);
    });
  }

  function drawBondTag(x, y, label, color, isDark, align) {
    simCtx.save();
    const lines = label.split('\n');
    const lineH = 12;
    simCtx.font = 'bold 10px sans-serif';
    const w = Math.max(...lines.map(l => simCtx.measureText(l).width)) + 12;
    const h = lines.length * lineH + 8;
    if (align === 'left') x += w / 2; // x를 이름표 왼쪽 끝으로 사용
    roundRect(simCtx, x - w / 2, y - h / 2, w, h, 6);
    simCtx.fillStyle = isDark ? '#1e293b' : '#ffffff';
    simCtx.fill();
    simCtx.lineWidth = 1.5;
    simCtx.strokeStyle = color;
    simCtx.stroke();
    simCtx.fillStyle = isDark && color === '#2563eb' ? '#60a5fa' : color;
    simCtx.textAlign = 'center';
    simCtx.textBaseline = 'middle';
    lines.forEach((l, i) => simCtx.fillText(l, x, y + (i - (lines.length - 1) / 2) * lineH));
    simCtx.restore();
  }

  function updateAndDrawWater(isDark) {
    for (let i = state.waterParticles.length - 1; i >= 0; i--) {
      const p = state.waterParticles[i];
      p.update();
      if (!p.isAlive) state.waterParticles.splice(i, 1);
      else if (state.showWater) p.draw(simCtx, isDark); // 숨겨도 진행(가수분해 타이밍)은 유지
    }
  }

  // --------------------------------------------------------------------------
  // 15. 판서
  // --------------------------------------------------------------------------
  function renderDrawCanvas() {
    drawCtx.save();
    drawCtx.setTransform(state.dpr, 0, 0, state.dpr, 0, 0);
    drawCtx.clearRect(0, 0, state.width, state.height);
    drawCtx.translate(state.view.offsetX, state.view.offsetY);
    drawCtx.scale(state.view.scale, state.view.scale);
    drawCtx.lineCap = 'round';
    drawCtx.lineJoin = 'round';
    state.strokes.forEach(s => drawSingleStroke(drawCtx, s));
    if (state.currentStroke && !state.currentStroke.isLaser) drawSingleStroke(drawCtx, state.currentStroke);

    // 레이저 필기: 일반 필기 위에 그림 (지우개 영향 없음)
    //  - 쓰는 중이거나 마지막 레이저 필기 후 LASER.HOLD 동안은 그대로, 이후 LASER.FADE 동안 서서히 사라짐
    //  - 이어서 쓰는 동안에는 앞서 쓴 레이저 글씨도 함께 유지되어 단어·문장이 한꺼번에 사라짐
    const now = nowMs();
    const writing = state.currentStroke && state.currentStroke.isLaser;
    let alpha = 1;
    if (!writing) {
      const t = now - state.lastLaserEnd;
      alpha = t <= LASER.HOLD ? 1 : Math.max(0, 1 - (t - LASER.HOLD) / LASER.FADE);
      if (alpha === 0) state.laserStrokes = [];
    }
    state.laserStrokes.forEach(s => drawLaserStroke(drawCtx, s, alpha));
    if (writing) drawLaserStroke(drawCtx, state.currentStroke, 1);
    drawCtx.restore();
  }

  const LASER = { HOLD: 1500, FADE: 1000 }; // 레이저: 유지 시간 · 사라지는 시간 (ms)

  // 펜 색 '기본(auto)'은 테마에 따라 검정/흰색으로 그려 항상 보이게 함
  const resolvePenColor = (color) =>
    color === 'auto' ? (state.theme === 'dark' ? '#f8fafc' : '#1e293b') : color;

  function strokePath(ctx, points) {
    ctx.beginPath();
    ctx.moveTo(points[0].x, points[0].y);
    for (let i = 1; i < points.length; i++) {
      const p1 = points[i - 1], p2 = points[i];
      ctx.quadraticCurveTo(p1.x, p1.y, (p1.x + p2.x) / 2, (p1.y + p2.y) / 2);
    }
    if (points.length === 1) ctx.lineTo(points[0].x + 0.01, points[0].y); // 점 하나도 보이게
  }

  // 레이저 필기: 빛나는 테두리 + 밝은 심
  function drawLaserStroke(ctx, stroke, alpha) {
    if (!stroke.points || stroke.points.length < 1 || alpha <= 0) return;
    const color = resolvePenColor(stroke.color);
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    strokePath(ctx, stroke.points);
    ctx.shadowColor = color;
    ctx.shadowBlur = 14;
    ctx.strokeStyle = color;
    ctx.lineWidth = stroke.width + 3;
    ctx.stroke();
    ctx.shadowBlur = 0;
    ctx.strokeStyle = 'rgba(255,255,255,0.85)';
    ctx.lineWidth = Math.max(1, stroke.width * 0.45);
    ctx.stroke();
    ctx.restore();
  }

  function drawSingleStroke(ctx, stroke) {
    if (!stroke.points || stroke.points.length < 2) return;
    ctx.save();
    if (stroke.isEraser) {
      ctx.globalCompositeOperation = 'destination-out';
      ctx.strokeStyle = 'rgba(0,0,0,1)';
      ctx.lineWidth = stroke.width * 3;
    } else {
      ctx.globalCompositeOperation = 'source-over';
      ctx.strokeStyle = resolvePenColor(stroke.color);
      ctx.lineWidth = stroke.width;
    }
    ctx.beginPath();
    ctx.moveTo(stroke.points[0].x, stroke.points[0].y);
    for (let i = 1; i < stroke.points.length; i++) {
      const p1 = stroke.points[i - 1], p2 = stroke.points[i];
      ctx.quadraticCurveTo(p1.x, p1.y, (p1.x + p2.x) / 2, (p1.y + p2.y) / 2);
    }
    ctx.stroke();
    ctx.restore();
  }

  // --------------------------------------------------------------------------
  // 16. 이벤트 바인딩
  // --------------------------------------------------------------------------
  function bindEventListeners() {
    dom.themeToggleBtn.addEventListener('click', () => {
      state.theme = state.theme === 'light' ? 'dark' : 'light';
      dom.body.className = `theme-${state.theme}`;
      dom.themeToggleBtn.querySelector('.theme-icon').textContent = state.theme === 'light' ? '🌙' : '☀️';
      renderDrawCanvas();
    });

    dom.collapseSidebarBtn.addEventListener('click', () => {
      dom.sidebar.classList.add('collapsed');
      setTimeout(resizeCanvases, 260);
    });
    dom.expandSidebarBtn.addEventListener('click', () => {
      dom.sidebar.classList.remove('collapsed');
      setTimeout(resizeCanvases, 260);
    });

    dom.catTabs.forEach(tab => tab.addEventListener('click', () => setCategory(tab.dataset.category)));

    dom.modeFormulaBtn.addEventListener('click', () => setMode('formula'));
    dom.modeSimpleBtn.addEventListener('click', () => setMode('simple'));
    dom.labelOnBtn.addEventListener('click', () => setBondLabels(true));
    dom.labelOffBtn.addEventListener('click', () => setBondLabels(false));
    dom.waterOnBtn.addEventListener('click', () => setWaterVisible(true));
    dom.waterOffBtn.addEventListener('click', () => setWaterVisible(false));
    dom.chOnBtn.addEventListener('click', () => setShowCH(true));
    dom.chOffBtn.addEventListener('click', () => setShowCH(false));

    // 단계 진행
    dom.stepPrevBtn.addEventListener('click', prevStep);
    dom.miniPrevBtn.addEventListener('click', prevStep);
    dom.stepNextBtn.addEventListener('click', () => { stopAutoPlay(); nextStep(); });
    dom.miniNextBtn.addEventListener('click', () => { stopAutoPlay(); nextStep(); });
    dom.stepPlayBtn.addEventListener('click', toggleAutoPlay);
    dom.miniPlayBtn.addEventListener('click', toggleAutoPlay);

    dom.separateBondsBtn.addEventListener('click', separateAllBonds);
    dom.clearAllMolsBtn.addEventListener('click', clearAll);
    dom.quickClearBtn.addEventListener('click', clearAll);

    document.querySelectorAll('.add-mol-btn').forEach(btn => {
      btn.addEventListener('click', () => addSingleMolecule(btn.dataset.type));
    });
    document.querySelectorAll('.preset-btn').forEach(btn => {
      btn.addEventListener('click', () => loadPreset(btn.dataset.preset));
    });

    dom.zoomInBtn.addEventListener('click', () => zoomAt(1.25, state.width / 2, state.height / 2));
    dom.zoomOutBtn.addEventListener('click', () => zoomAt(0.8, state.width / 2, state.height / 2));
    dom.zoomResetBtn.addEventListener('click', fitView);

    dom.drawModeBtn.addEventListener('click', () => {
      state.drawMode = !state.drawMode;
      dom.drawModeBtn.classList.toggle('active', state.drawMode);
      dom.drawOptionsPanel.classList.toggle('active', state.drawMode);
      dom.drawCanvas.classList.toggle('draw-active', state.drawMode);
      showHint(state.drawMode ? '✏️ 판서 모드: 분자에 영향을 주지 않고 자유롭게 필기하세요. (두 손가락으로 화면 이동)' : '분자 조작 모드로 복귀했습니다.');
    });

    dom.colorDots.forEach(dot => {
      dot.addEventListener('click', () => {
        dom.colorDots.forEach(d => d.classList.remove('active'));
        dot.classList.add('active');
        state.penColor = dot.dataset.color;
        state.isEraser = false;
        dom.eraserBtn.classList.remove('active');
      });
    });

    dom.widthBtns.forEach(btn => {
      btn.addEventListener('click', () => {
        dom.widthBtns.forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        state.penWidth = parseInt(btn.dataset.width, 10);
      });
    });

    dom.eraserBtn.addEventListener('click', () => {
      state.isEraser = !state.isEraser;
      if (state.isEraser) state.isLaser = false; // 지우개와 레이저는 동시에 켜지지 않음
      dom.eraserBtn.classList.toggle('active', state.isEraser);
      dom.laserBtn.classList.toggle('active', state.isLaser);
    });

    dom.laserBtn.addEventListener('click', () => {
      state.isLaser = !state.isLaser;
      if (state.isLaser) state.isEraser = false;
      dom.laserBtn.classList.toggle('active', state.isLaser);
      dom.eraserBtn.classList.toggle('active', state.isEraser);
      showHint(state.isLaser
        ? '🔦 레이저 포인터: 쓴 글씨가 잠시 뒤 서서히 사라집니다. 이어서 쓰는 동안에는 함께 유지됩니다.'
        : '✏️ 일반 펜으로 돌아왔습니다.');
    });

    dom.showHintBtn.addEventListener('click', toggleHint);

    dom.clearDrawBtn.addEventListener('click', () => {
      state.strokes = [];
      state.laserStrokes = [];
      renderDrawCanvas();
      showHint('판서 내용이 모두 지워졌습니다.');
    });

    // 휠 줌 (캔버스 기준 좌표로 변환)
    dom.canvasWrapper.addEventListener('wheel', (e) => {
      e.preventDefault();
      const s = clientToScreen(e.clientX, e.clientY);
      zoomAt(e.deltaY < 0 ? 1.12 : 0.89, s.x, s.y);
    }, { passive: false });

    setupPointerEvents();
  }

  function setShowCH(on) {
    state.showCH = on;
    dom.chOnBtn.classList.toggle('active', on);
    dom.chOffBtn.classList.toggle('active', !on);
    if (on && state.displayMode === 'simple') showHint('💡 C·H 표시는 화학 구조식 모드에서 보입니다.');
  }

  function setWaterVisible(on) {
    state.showWater = on;
    dom.waterOnBtn.classList.toggle('active', on);
    dom.waterOffBtn.classList.toggle('active', !on);
  }

  function setBondLabels(on) {
    state.showBondLabels = on;
    dom.labelOnBtn.classList.toggle('active', on);
    dom.labelOffBtn.classList.toggle('active', !on);
  }

  function setMode(mode) {
    state.displayMode = mode;
    dom.modeFormulaBtn.classList.toggle('active', mode === 'formula');
    dom.modeSimpleBtn.classList.toggle('active', mode === 'simple');
  }

  // --------------------------------------------------------------------------
  // 17. 포인터 인터랙션 (마우스·터치·펜 통합)
  // --------------------------------------------------------------------------
  function setupPointerEvents() {
    const wrapper = dom.canvasWrapper;

    // 입력 종류별 기준값
    //  - 펜슬은 손가락보다 누르는 시간이 길고 펜 끝이 미세하게 떨려서 기준을 넉넉하게 둠
    const DOUBLE_TAP_MS = { mouse: 350, touch: 380, pen: 500 }; // 앞 탭을 뗀 뒤 다음 탭을 누르기까지
    const DOUBLE_TAP_DIST = { mouse: 12, touch: 40, pen: 40 };  // 두 탭 사이 허용 거리 (화면 px)
    const DRAG_SLOP = { mouse: 3, touch: 10, pen: 8 };           // 이만큼 움직여야 드래그로 판단
    const typeOf = (e) => (e.pointerType === 'pen' || e.pointerType === 'touch') ? e.pointerType : 'mouse';

    const touchPoints = () => Array.from(state.pointers.values()).filter(p => p.type === 'touch');
    const hasPen = () => Array.from(state.pointers.values()).some(p => p.type === 'pen');

    const pinchInfo = () => {
      const pts = touchPoints().slice(0, 2);
      const a = clientToScreen(pts[0].x, pts[0].y);
      const b = clientToScreen(pts[1].x, pts[1].y);
      return {
        dist: Math.hypot(a.x - b.x, a.y - b.y),
        center: { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 }
      };
    };

    const findMolAt = (wx, wy) => {
      for (let i = state.molecules.length - 1; i >= 0; i--) {
        if (state.molecules[i].containsPoint(wx, wy)) return state.molecules[i];
      }
      return null;
    };

    const endInteraction = (commitStroke) => {
      const s = state.currentStroke;
      if (s && commitStroke) {
        if (s.isLaser) {
          state.laserStrokes.push(s);
          state.lastLaserEnd = nowMs();
        } else {
          state.strokes.push(s);
        }
      }
      state.currentStroke = null;
      state.draggedMol = null;
      state.isPanning = false;
      dom.simCanvas.classList.remove('grabbing');
      renderDrawCanvas();
    };

    // 더블클릭/더블탭 처리: 결합되어 있으면 분리(가수분해), 단독 분자면 삭제
    let lastDoubleHandled = 0;
    const handleDoubleTap = (mol) => {
      lastDoubleHandled = Date.now();
      state.lastTap = { time: 0, mol: null, x: 0, y: 0 };
      stopAutoPlay();
      if (!separateMoleculeBonds(mol)) removeMolecule(mol);
    };

    let doubleTapPointer = null; // 더블탭으로 처리된 포인터 (뗄 때 새 탭으로 기록하지 않음)

    wrapper.addEventListener('pointerdown', (e) => {
      if (e.pointerType === 'mouse' && e.button !== 0) return;
      e.preventDefault();
      const type = typeOf(e);

      // 손바닥 무시: 펜슬로 쓰는 중에 닿는 손가락(손바닥)은 무시
      if (type === 'touch' && hasPen()) return;

      // 뗄 때 이벤트를 놓쳐 남아 있는 포인터 정리 (펜·마우스는 하나뿐, 첫 손가락이면 이전 손가락 기록은 무효)
      if (type !== 'touch' || e.isPrimary) {
        for (const [id, p] of state.pointers) if (p.type === type) state.pointers.delete(id);
      }
      // 펜슬이 닿으면 손바닥으로 시작된 동작(이동·핀치)을 취소
      if (type === 'pen' && touchPoints().length) {
        for (const [id, p] of state.pointers) if (p.type === 'touch') state.pointers.delete(id);
        state.isPinching = false;
        state.lastPinchDist = null;
        state.lastPinchCenter = null;
        endInteraction(false);
      }

      state.pointers.set(e.pointerId, { x: e.clientX, y: e.clientY, type });
      try { wrapper.setPointerCapture(e.pointerId); } catch (_) { /* 지원하지 않는 환경 */ }

      // 두 손가락: 진행 중이던 드래그/필기를 취소하고 핀치 줌 & 이동
      if (type === 'touch' && touchPoints().length === 2) {
        endInteraction(false);
        const p = pinchInfo();
        state.isPinching = true;
        state.lastPinchDist = p.dist;
        state.lastPinchCenter = p.center;
        return;
      }
      if (state.isPinching || state.pointers.size > 1) return;

      const s = clientToScreen(e.clientX, e.clientY);
      const wc = screenToWorld(s.x, s.y);
      state.downScreen = { x: e.clientX, y: e.clientY };
      state.dragMoved = false;

      if (state.drawMode) {
        state.currentStroke = {
          color: state.penColor, width: state.penWidth,
          isEraser: state.isEraser, isLaser: state.isLaser && !state.isEraser, points: [wc]
        };
        if (state.currentStroke.isLaser) renderDrawCanvas();
        return;
      }

      const found = findMolAt(wc.x, wc.y);

      // 더블클릭 / 더블탭: 같은 분자를 앞 탭을 뗀 직후 다시 누름 (손가락·펜슬·마우스 공통)
      const now = Date.now();
      const lt = state.lastTap;
      if (found && found === lt.mol && now - lt.time < DOUBLE_TAP_MS[type] &&
          Math.hypot(e.clientX - lt.x, e.clientY - lt.y) < DOUBLE_TAP_DIST[type]) {
        doubleTapPointer = e.pointerId;
        handleDoubleTap(found);
        return;
      }

      if (found) {
        state.draggedMol = found;
        state.dragOffset.x = wc.x - found.x;
        state.dragOffset.y = wc.y - found.y;
      } else {
        state.isPanning = true;
        state.panStart.x = e.clientX;
        state.panStart.y = e.clientY;
      }
      dom.simCanvas.classList.add('grabbing');
    });

    const onMove = (e) => {
      if (!state.pointers.has(e.pointerId)) return;
      const ptr = state.pointers.get(e.pointerId);
      ptr.x = e.clientX;
      ptr.y = e.clientY;

      if (state.isPinching) {
        if (ptr.type !== 'touch' || touchPoints().length < 2) return;
        const p = pinchInfo();
        if (state.lastPinchDist) zoomAt(p.dist / state.lastPinchDist, p.center.x, p.center.y);
        state.view.offsetX += p.center.x - state.lastPinchCenter.x;
        state.view.offsetY += p.center.y - state.lastPinchCenter.y;
        state.lastPinchDist = p.dist;
        state.lastPinchCenter = p.center;
        renderDrawCanvas();
        return;
      }

      const s = clientToScreen(e.clientX, e.clientY);
      const wc = screenToWorld(s.x, s.y);

      if (state.drawMode && state.currentStroke) {
        state.currentStroke.points.push(wc);
        renderDrawCanvas();
        return;
      }

      // 펜 끝·손가락의 미세한 떨림은 드래그로 보지 않음 (탭/더블탭이 정확히 인식되도록)
      if (!state.dragMoved) {
        const d = Math.hypot(e.clientX - state.downScreen.x, e.clientY - state.downScreen.y);
        if (d < DRAG_SLOP[ptr.type]) return;
        state.dragMoved = true;
        if (state.isPanning) { state.panStart.x = e.clientX; state.panStart.y = e.clientY; }
      }

      if (state.draggedMol) {
        const m = state.draggedMol;
        moveGroup(m.groupId, wc.x - state.dragOffset.x - m.x, wc.y - state.dragOffset.y - m.y);
        if (checkAndPerformMagneticSnap(m)) {
          // 스냅으로 위치가 바뀌었으므로 손가락 기준점을 다시 잡아 튀는 현상 방지
          state.dragOffset.x = wc.x - m.x;
          state.dragOffset.y = wc.y - m.y;
        }
        return;
      }

      if (state.isPanning) {
        state.view.offsetX += e.clientX - state.panStart.x;
        state.view.offsetY += e.clientY - state.panStart.y;
        state.panStart.x = e.clientX;
        state.panStart.y = e.clientY;
        renderDrawCanvas();
      }
    };

    const onUp = (e) => {
      if (!state.pointers.has(e.pointerId)) return;
      state.pointers.delete(e.pointerId);
      try { wrapper.releasePointerCapture(e.pointerId); } catch (_) { /* 이미 해제됨 */ }

      if (state.isPinching) {
        // 손가락을 모두 뗄 때까지 다른 동작을 시작하지 않음
        if (touchPoints().length === 0) {
          state.isPinching = false;
          state.lastPinchDist = null;
          state.lastPinchCenter = null;
        }
        return;
      }

      if (doubleTapPointer === e.pointerId) {
        doubleTapPointer = null;
        endInteraction(true);
        return;
      }

      const mol = state.draggedMol;
      if (mol && state.dragMoved) {
        // 실제로 끌어다 놓았을 때만 결합 확인 · 안내 (단순 클릭에는 안내하지 않음)
        if (!checkAndPerformMagneticSnap(mol)) explainNoBond(mol);
      }

      // 움직이지 않고 뗀 탭만 더블탭 판정 기준으로 기록
      if (!state.drawMode && !state.dragMoved) {
        state.lastTap = { time: Date.now(), mol, x: e.clientX, y: e.clientY };
      } else {
        state.lastTap = { time: 0, mol: null, x: 0, y: 0 };
      }
      endInteraction(true);
    };

    // 보조: 브라우저가 dblclick을 보내는 경우 (위 판정이 놓친 경우에만 처리)
    wrapper.addEventListener('dblclick', (e) => {
      if (state.drawMode || Date.now() - lastDoubleHandled < 700) return;
      const s = clientToScreen(e.clientX, e.clientY);
      const wc = screenToWorld(s.x, s.y);
      const mol = findMolAt(wc.x, wc.y);
      if (mol) handleDoubleTap(mol);
    });

    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
    window.addEventListener('pointercancel', onUp);
  }

  // --------------------------------------------------------------------------
  // 18. UI 헬퍼
  // --------------------------------------------------------------------------
  // 카테고리별 작업 공간 (분자·결합·판서·화면 위치를 각각 따로 보관)
  const workspaces = {};

  function saveWorkspace(cat) {
    workspaces[cat] = {
      molecules: state.molecules,
      bonds: state.bonds,
      strokes: state.strokes,
      currentPreset: state.currentPreset,
      history: state.history,
      view: { scale: state.view.scale, offsetX: state.view.offsetX, offsetY: state.view.offsetY }
    };
  }

  function restoreWorkspace(cat) {
    const ws = workspaces[cat];
    state.waterParticles = [];
    state.slides = [];
    state.draggedMol = null;
    state.isPanning = false;
    state.currentStroke = null;
    state.laserStrokes = [];
    state.recentSplits = [];
    state.lastTap = { time: 0, mol: null, x: 0, y: 0 };

    if (ws) {
      state.molecules = ws.molecules;
      state.bonds = ws.bonds;
      state.strokes = ws.strokes;
      state.currentPreset = ws.currentPreset;
      state.history = ws.history || [];
      state.view.scale = ws.view.scale;
      state.view.offsetX = ws.view.offsetX;
      state.view.offsetY = ws.view.offsetY;
      updateZoomIndicator();
      renderDrawCanvas();
      showHint('이전에 작업하던 화면을 불러왔습니다.');
    } else {
      // 처음 여는 카테고리: 기본 분자를 결합하지 않은 상태로 배치
      state.molecules = defaultMolecules(cat);
      state.bonds = [];
      state.history = [];
      state.strokes = [];
      state.currentPreset = null;
      fitView();
      const hints = {
        free: '🧪 자유 모드: 왼쪽에서 단당류·아미노산·지질 성분을 자유롭게 불러오세요. 같은 종류끼리 맞닿게 하면 결합합니다.',
        carbs: '💡 포도당 2개가 준비되어 있습니다. 맞닿게 드래그하면 결합합니다.',
        protein: '💡 아미노산 2개(글리신, 알라닌)가 준비되어 있습니다. 맞닿게 드래그하면 펩타이드 결합합니다.',
        lipid: '💡 글리세롤 1개와 포화 지방산 3개가 준비되어 있습니다. 지방산의 HO를 글리세롤의 OH에 맞닿게 드래그하세요.'
      };
      showHint(hints[cat]);
    }
  }

  // 카테고리별 기본 화면 (결합하지 않은 상태)
  function defaultMolecules(cat) {
    if (cat === 'free') return [];
    if (cat === 'protein') {
      return [makeAmino(AMINO_ACIDS[0], -150, 0), makeAmino(AMINO_ACIDS[1], 150, 0)];
    }
    if (cat === 'lipid') {
      return [
        makeLipidPart('glycerol', -180, 0),
        makeLipidPart('fatty_sat', 160, -75, '포화 지방산 1'),
        makeLipidPart('fatty_sat', 160, 0, '포화 지방산 2'),
        makeLipidPart('fatty_sat', 160, 75, '포화 지방산 3')
      ];
    }
    return [makeCarb('glucose', -150, 0), makeCarb('glucose', 150, 0)];
  }

  function setCategory(cat) {
    if (cat !== state.activeCategory) {
      stopAutoPlay();
      finishPendingWork();
      saveWorkspace(state.activeCategory);
      state.activeCategory = cat;
      restoreWorkspace(cat);
    }
    dom.catTabs.forEach(tab => tab.classList.toggle('active', tab.dataset.category === cat));
    Object.keys(dom.panels).forEach(key => dom.panels[key].classList.toggle('active', key === cat));
  }

  // 하단 설명칸: 표시 후 5초 뒤 자동으로 숨김, '설명 보기' 버튼으로 다시 표시
  const HINT_DURATION = 5000;
  let hintTimer = null;

  function hideHint() {
    if (hintTimer) clearTimeout(hintTimer);
    hintTimer = null;
    dom.hintBar.classList.add('hidden');
    dom.showHintBtn.classList.remove('active');
    dom.showHintBtn.textContent = '💡 설명 보기';
  }

  function revealHint() {
    dom.hintBar.classList.remove('hidden');
    dom.showHintBtn.classList.add('active');
    dom.showHintBtn.textContent = '🙈 설명 감추기';
    if (hintTimer) clearTimeout(hintTimer);
    hintTimer = setTimeout(hideHint, HINT_DURATION);
  }

  // 설명이 보이는 중이면 바로 감추고, 숨겨져 있으면 다시 보이기
  function toggleHint() {
    if (dom.hintBar.classList.contains('hidden')) revealHint();
    else hideHint();
  }

  function showHint(msg) {
    dom.hintText.textContent = msg;
    revealHint();
  }

  // 새 분자 배치: 가장 오른쪽 분자의 오른쪽에 약간 떨어뜨려 놓음 (결합 거리 밖이라 저절로 붙지 않음)
  // 자유 모드: 지금 보고 있는 화면 안에서 다른 분자와 겹치지 않는 빈 자리 찾기
  //  - 화면 가운데에서 바깥쪽으로 나선형으로 탐색
  //  - 다른 분자와 SPOT_MARGIN 이상 떨어뜨려 손을 대도 저절로 결합하지 않게 함
  const SPOT_MARGIN = 70;
  const nameExtraOf = (m) => (m.subType === 'fatty_sat' || m.subType === 'fatty_unsat') ? 100 : 0;

  function findFreeSpot(w, h, extraRight = 0) {
    const tl = screenToWorld(16, 76);                              // 상단 도구 막대 아래
    const br = screenToWorld(state.width - 16, state.height - 64); // 하단 설명칸 위
    if (br.x - tl.x < w + extraRight || br.y - tl.y < h) return null;
    const cx0 = (tl.x + br.x - extraRight) / 2, cy0 = (tl.y + br.y) / 2;
    const step = 30;
    const maxK = Math.ceil(Math.max(br.x - tl.x, br.y - tl.y) / 2 / step) + 1;

    const fits = (x, y) => {
      if (x - w / 2 < tl.x || x + w / 2 + extraRight > br.x || y - h / 2 < tl.y || y + h / 2 > br.y) return false;
      return !state.molecules.some(m => {
        const ml = m.x - m.width / 2, mr = m.x + m.width / 2 + nameExtraOf(m);
        const mt = m.y - m.height / 2, mb = m.y + m.height / 2;
        return x - w / 2 < mr + SPOT_MARGIN && x + w / 2 + extraRight > ml - SPOT_MARGIN &&
               y - h / 2 < mb + SPOT_MARGIN && y + h / 2 > mt - SPOT_MARGIN;
      });
    };

    for (let k = 0; k <= maxK; k++) {
      for (let i = -k; i <= k; i++) {
        for (let j = -k; j <= k; j++) {
          if (Math.max(Math.abs(i), Math.abs(j)) !== k) continue; // 정사각형 고리만
          const x = cx0 + i * step, y = cy0 + j * step;
          if (fits(x, y)) return { x, y };
        }
      }
    }
    return null;
  }

  function placeNewMolecule(mol) {
    const spot = state.activeCategory === 'free' ? findFreeSpot(mol.width, mol.height, nameExtraOf(mol)) : null;
    if (spot) {
      mol.x = spot.x;
      mol.y = spot.y;
    } else if (state.molecules.length === 0) {
      const c = screenToWorld(state.width / 2, state.height / 2);
      mol.x = c.x;
      mol.y = c.y;
    } else {
      const rightmost = state.molecules.reduce((a, m) => (m.x + m.width / 2 > a.x + a.width / 2 ? m : a));
      mol.x = rightmost.x + rightmost.width / 2 + state.SPAWN_GAP + mol.width / 2;
      mol.y = rightmost.y;
    }
    state.currentPreset = null;
    state.molecules.push(mol);
    state.history.push({ type: 'add', mols: [mol] });

    // 새 분자가 화면 밖에 있으면 화면 맞춤
    const left = (mol.x - mol.width / 2) * state.view.scale + state.view.offsetX;
    const right = (mol.x + mol.width / 2) * state.view.scale + state.view.offsetX;
    const top = (mol.y - mol.height / 2) * state.view.scale + state.view.offsetY;
    const bottom = (mol.y + mol.height / 2) * state.view.scale + state.view.offsetY;
    if (left < 0 || right > state.width || top < 0 || bottom > state.height) fitView();
  }

  // 자유 모드: 세포막(인지질 2중층) 조각 추가 - 기존 분자들 아래에 한 덩어리로 배치
  function addMembrane() {
    const n = PL_UNIT.COUNT;  // 지질 탭의 세포막과 같은 길이·크기
    const gap = PL_UNIT.HEAD_R * 2 + PL_UNIT.HEAD_GAP, len = PL_UNIT.LEN;
    const half = len / 2 + PL_UNIT.LAYER_GAP / 2;   // 막 중심 ~ 각 층 중심
    let cx, cy;
    const totalW = (n - 1) * gap + gap, totalH = 2 * half + len;
    const spot = findFreeSpot(totalW, totalH);   // 보고 있는 화면 안 빈 자리 (세포막이 화면보다 크면 없음)
    if (spot) {
      cx = spot.x; cy = spot.y;
    } else if (state.molecules.length === 0) {
      const c = screenToWorld(state.width / 2, state.height / 2);
      cx = c.x; cy = c.y;
    } else {
      let minX = Infinity, maxX = -Infinity, maxY = -Infinity;
      state.molecules.forEach(m => {
        minX = Math.min(minX, m.x - m.width / 2);
        maxX = Math.max(maxX, m.x + m.width / 2);
        maxY = Math.max(maxY, m.y + m.height / 2);
      });
      cx = (minX + maxX) / 2;
      cy = maxY + 80 + half + len / 2;             // 기존 분자 아래 80px 띄움
    }
    const groupId = 'mem_' + Math.random().toString(36).slice(2, 9);
    const start = cx - ((n - 1) * gap) / 2;
    const units = [];
    for (let i = 0; i < n; i++) {
      units.push(
        new Molecule({ category: 'lipid', subType: 'pl_unit', name: '인지질(상)', x: start + i * gap, y: cy - half, width: gap, height: len, data: { dir: 'down', fixedGroup: groupId } }),
        new Molecule({ category: 'lipid', subType: 'pl_unit', name: '인지질(하)', x: start + i * gap, y: cy + half, width: gap, height: len, data: { dir: 'up', fixedGroup: groupId } })
      );
    }
    units.forEach(u => { u.groupId = groupId; });
    state.molecules.push(...units);
    state.history.push({ type: 'add', mols: units });
    state.currentPreset = null;

    // 화면 밖이면 화면 맞춤
    const sx = (x) => x * state.view.scale + state.view.offsetX;
    const sy = (y) => y * state.view.scale + state.view.offsetY;
    const left = sx(start - gap / 2), right = sx(start + (n - 1) * gap + gap / 2);
    const top = sy(cy - half - len / 2), bottom = sy(cy + half + len / 2);
    if (left < 0 || right > state.width || top < 0 || bottom > state.height) fitView();
    showHint('🫧 세포막(인지질 2중층)을 추가했습니다. 친수성 머리는 바깥, 소수성 꼬리는 안쪽을 향합니다. 드래그하면 통째로 움직이고, 더블클릭하면 삭제됩니다.');
  }

  function addSingleMolecule(type) {
    let mol = null;
    if (type === 'glucose' || type === 'fructose' || type === 'galactose') mol = makeCarb(type, 0, 0);
    else if (type === 'glucose_alpha') mol = makeCarb('glucose', 0, 0, { anomer: 'alpha', name: 'α-포도당' });
    else if (type === 'glucose_beta') mol = makeCarb('glucose', 0, 0, { anomer: 'beta', name: 'β-포도당' });
    else if (type === 'membrane') { addMembrane(); return; }
    else if (['glycerol', 'fatty_sat', 'fatty_unsat', 'phosphate'].includes(type)) mol = makeLipidPart(type, 0, 0);

    if (mol) {
      placeNewMolecule(mol);
      showHint(`[${mol.name}] 추가됨. 다른 분자에 맞닿을 만큼 드래그하면 결합합니다!`);
    }
  }

  // 아미노산 팔레트 (단백질 탭 + 자유 모드 탭)
  function setupAminoAcidPalette() {
    [dom.aminoPalette, dom.freeAminoPalette].forEach(fillAminoPalette);
  }

  function fillAminoPalette(container) {
    if (!container) return;
    container.innerHTML = '';
    AMINO_ACIDS.forEach(aa => {
      const btn = document.createElement('button');
      btn.className = `aa-btn aa-${aa.type}`;
      btn.innerHTML = `<strong>${aa.code}</strong><span>${aa.name}</span>`;
      btn.title = `${aa.name} (${aa.rGroup})`;
      btn.addEventListener('click', () => {
        placeNewMolecule(makeAmino(aa, 0, 0));
        showHint(`아미노산 [${aa.name}] 추가됨. 다른 아미노산에 맞닿을 만큼 드래그해 펩타이드 결합을 형성해보세요!`);
      });
      container.appendChild(btn);
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
