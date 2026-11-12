let kanjiData = [], groups = [], partsInfo = null;
const state = { groups: new Set(), chars: new Set(), tags: new Set(), readings: [], rmode: 'or', rads: new Set(), xchars: new Set(), xgroups: new Set(), strokes: new Set(), tagFirst: false };
let compact = false;           // コンパクト表示（この端末のブラウザに保存）
try { compact = localStorage.getItem('kanjiView') === 'compact'; } catch (e) {}
let meanings = {};             // 漢字 → {m:字義, place:国名・都市名}
let yomiExtra = {};            // 漢字 → 作者が追加した読み（名乗り読みの先頭に表示）
const NC = { cache: 'no-cache' };   // JSONは毎回「更新があるか」を確認する（古い表示が残らないように）
const radCount = new Map();   // 部首番号ごとの漢字数
const strokeCount = new Map(); // 画数ごとの漢字数
const kanjiMap = new Map();   // 漢字 → データ
let tagCats = [];             // [{name, tags:[{name, desc}]}]
const tagCat = new Map();     // タグ → カテゴリ名
const tagCount = new Map();   // タグ → 漢字数
let favList = [];             // お気に入り（追加した順）
let selKind = '';             // 共通の選択画面で今開いているもの（tag / rad / stroke）
const viaInput = new Set();   // 入力欄からEnterで追加したパーツ（グループ提案の対象）
const openGroups = new Set();
let charToGroup = new Map(), partFreq = new Map(), groupMap = new Map();
const PAGE = 120;               // 一度に表示する件数
let lastResults = [], shown = 0;
let timer = null, composing = false;

// 部首用の別コードの字を、ふつうの字に統一する対応表
const NORM = {'⺡':'氵','⺗':'忄','⺾':'艹','⻌':'辶','⺨':'犭','⻟':'飠'};
const norm = c => NORM[c] || c;
// カタカナ→ひらがな、「.」「-」を除去（読み検索用）
const toHira = s => s.replace(/[ァ-ヶ]/g, c => String.fromCharCode(c.charCodeAt(0) - 0x60)).replace(/[.\-]/g, '');
const $ = id => document.getElementById(id);

// ---- 部首番号（康熙部首 1〜214。並び順＝番号。同じ部首の異体字はスペース区切り）----
const BUSHU = ["一", "丨", "丶", "丿", "乙", "亅", "二", "亠", "人 亻", "儿", "入", "八", "冂", "冖", "冫", "几", "凵", "刀 刂", "力", "勹", "匕", "匚", "匸", "十", "卜", "卩", "厂", "厶", "又", "口", "囗", "土", "士", "夂", "夊", "夕", "大", "女", "子", "宀", "寸", "小", "尢 尣", "尸", "屮", "山", "巛 川", "工", "己 已 巳", "巾", "干", "幺", "广", "廴", "廾", "弋", "弓", "彐 彐 彑", "彡", "彳", "心 忄", "戈", "戶 戸", "手 扌", "支", "攴 攵", "文", "斗", "斤", "方", "无 旡", "日", "曰", "月", "木", "欠", "止", "歹 歺", "殳", "毋 母", "比", "毛", "氏", "气", "水 氵 氺", "火 灬", "爪 爫", "父", "爻", "爿", "片", "牙", "牛 牜", "犬 犭", "玄", "玉 王", "瓜", "瓦", "甘", "生", "用", "田", "疋", "疒", "癶", "白", "皮", "皿", "目 罒", "矛", "矢", "石", "示 礻", "禸", "禾", "穴", "立", "竹", "米", "糸", "缶", "网", "羊", "羽 羽", "老 耂", "而", "耒", "耳", "聿", "肉 月", "臣", "自", "至", "臼", "舌", "舛", "舟", "艮", "色", "艸 艹", "虍", "虫", "血", "行", "衣 衤", "襾 西 覀", "見", "角", "言 訁", "谷", "豆", "豕", "豸", "貝", "赤", "走", "足 𧾷", "身", "車", "辛", "辰", "辵 辶", "邑 阝", "酉", "釆", "里", "金 釒", "長", "門", "阜 阝", "隶", "隹", "雨", "靑 青", "非", "面", "革", "韋", "韭", "音", "頁", "風", "飛", "食 飠", "首", "香", "馬", "骨", "高", "髟", "鬥", "鬯", "鬲", "鬼", "魚", "鳥", "鹵", "鹿", "麥 麦", "麻", "黃 黄", "黍", "黑 黒", "黹", "黽", "鼎", "鼓", "鼠", "鼻", "齊 斉", "齒 歯", "龍 竜", "龜 亀", "龠"];
const RAD = new Map();
BUSHU.forEach((forms, i) => forms.split(/\s+/).forEach((t, k) => { if (!RAD.has(t) || k === 0) RAD.set(t, i + 1); }));
const collator = new Intl.Collator('ja');
// 各画数の最後の部首番号（1画〜17画）。番号順がそのまま画数順
const RADEND = [6, 29, 60, 94, 117, 146, 166, 175, 186, 194, 200, 204, 208, 210, 211, 213, 214];
const RADNOTE = { 74: 'つき', 130: 'にくづき', 163: 'おおざと', 170: 'こざと' };   // 同じ形（月・阝）を区別する注記
const radStrokes = n => RADEND.findIndex(e => n <= e) + 1;
const radLabel = n => {
  const f = [...new Set(BUSHU[n - 1].split(/\s+/))].filter(t => !(n === 130 && t === '月'));
  return f.join('・') + (RADNOTE[n] ? `（${RADNOTE[n]}）` : '');
};

// ---- 読みの整理 ----
// 「-ぞい」「はや-」のような接続形は表示も検索もしない
const isJoin = r => r.startsWith('-') || r.endsWith('-');
const usable = arr => (arr || []).filter(r => !isJoin(r));
// HTMLに埋め込む文字列は、記号を無害な形にしてから使う
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
// 作者が追加した読み
const extraOf = it => (yomiExtra[it.kanji] || []).filter(r => typeof r === 'string' && r);
// 名乗り読み：追加した読みを先頭に、重複（ひらがなにして同じもの）は除く
function nanoriOf(it) {
  const seen = new Set(), out = [];
  [...extraOf(it), ...usable(it.readings.nanori)].forEach(r => { const k = toHira(r); if (k && !seen.has(k)) { seen.add(k); out.push(r); } });
  return out;
}
// 送り仮名（「.」以降）を細く小さい文字にする： は.や.い → は<細>やい</細>
function okuriHTML(r) {
  const i = r.indexOf('.');
  if (i < 0) return esc(r);
  return esc(r.slice(0, i)) + '<span class="okuri">' + esc(r.slice(i + 1).replace(/\./g, '')) + '</span>';
}

// ---------- 読み込み ----------
async function loadData() {
  try {
    kanjiData = await (await fetch('data.json', NC)).json();
    // パーツ（構成要素）は別ファイル（ライセンスが異なるため）。読み込んで各漢字に付ける
    const cj = await (await fetch('components.json', NC)).json();
    kanjiData.forEach(it => { it.components = cj.components[it.kanji] || []; });
  } catch (e) {
    $('kanjiGrid').innerHTML = '<p class="error">data.json または components.json を読み込めませんでした。</p>';
    return;
  }
  // イメージタグ（別ファイル。無くても他の機能は使える）
  try {
    const tj = await (await fetch('tags.json', NC)).json();
    tagCats = tj.categories || [];
    kanjiData.forEach(it => { it.tags = (tj.kanji && tj.kanji[it.kanji]) || []; });
  } catch (e) { tagCats = []; kanjiData.forEach(it => { it.tags = []; }); }
  // 字義（別ファイル。無くても他の機能は使える）
  try { meanings = ((await (await fetch('meanings.json', NC)).json()).kanji) || {}; } catch (e) { meanings = {}; }
  // 作者が追加した読み（別ファイル。無くても他の機能は使える）
  try { yomiExtra = ((await (await fetch('yomi_extra.json', NC)).json()).readings) || {}; } catch (e) { yomiExtra = {}; }
  try { groups = await (await fetch('groups.json', NC)).json(); } catch (e) { groups = []; }
  try { partsInfo = await (await fetch('parts.json', NC)).json(); } catch (e) { partsInfo = null; }
  const sel = $('strokeSel');
  for (let i = 2; i <= 9; i++) sel.add(new Option(i + '画', i));
  sel.add(new Option('10画以上', 10));
  groups.forEach(g => { g.members = g.members.map(norm); g.members.forEach(m => charToGroup.set(m, g)); groupMap.set(g.id, g); });
  kanjiData.forEach(it => kanjiMap.set(it.kanji, it));
  kanjiData.forEach(it => strokeCount.set(it.strokes, (strokeCount.get(it.strokes) || 0) + 1));
  loadFavs(); updateFavCount();
  kanjiData.forEach(buildParts);
  kanjiData.forEach(it => radCount.set(it._rad, (radCount.get(it._rad) || 0) + 1));
  initTags();
  restoreFromURL();
  [...state.tags].forEach(t => { if (!tagCount.has(t)) state.tags.delete(t); });   // 名前を変えたタグ（古いURL）は外す
  update();
}

// 各漢字の「パーツ一覧」＝ components ＋ 部首欄
function buildParts(item) {
  const s = new Set();
  item.components.forEach(c => { c = (c || '').trim(); if (c) s.add(norm(c)); });
  const toks = item.radical.split(/\s+/).filter(Boolean);
  toks.forEach(t => { if (toks[0] === '肉' && t === '月') t = '⺼'; s.add(norm(t)); }); // 月とにくづきは別扱い
  item._parts = s;
  item._rad = RAD.get(toks[0]) || 999;   // 部首の先頭の字から番号を求める
  const first = usable(item.readings.on)[0] || usable(item.readings.kun)[0] || usable(item.readings.nanori)[0];
  item._yomi = first ? toHira(first.split('.')[0]) : '\uffff';   // 読みなしは最後
  // 読みは完全一致で探す。訓読み（は.る）は「はる」「は」のどちらでも当たる
  const rs = new Set();
  [...usable(item.readings.on), ...usable(item.readings.kun), ...usable(item.readings.nanori)].forEach(r => {
    const full = toHira(r); if (full) rs.add(full);
    if (r.includes('.')) { const stem = toHira(r.split('.')[0]); if (stem) rs.add(stem); }
  });
  extraOf(item).forEach(r => { const h = toHira(r); if (h) rs.add(h); });   // 追加した読みも検索の対象
  item._rs = rs;
  s.forEach(p => partFreq.set(p, (partFreq.get(p) || 0) + 1));
}

// タグの数を数える（タグの一覧そのものは、選択画面を開いたときに作る）
function initTags() {
  tagCat.clear(); tagCount.clear();
  tagCats.forEach(c => c.tags.forEach(t => tagCat.set(t.name, c.name)));
  kanjiData.forEach(k => k.tags.forEach(t => tagCount.set(t, (tagCount.get(t) || 0) + 1)));
  $('cntTag').textContent = kanjiData.filter(k => k.tags.length).length;
  $('cntMean').textContent = kanjiData.filter(k => meanings[k.kanji]).length;
  $('tagGroup').style.display = tagCount.size ? '' : 'none';   // タグが無い間は欄ごと隠す
}
function renderSelStrokes() {
  const box = $('selectedStrokes'); box.innerHTML = '';
  [...state.strokes].sort((a, b) => a - b).forEach(n => {
    const c = chipEl(); c.className = 'chip active'; c.textContent = n + '画 ×';
    c.onclick = () => { state.strokes.delete(n); update(); }; box.appendChild(c);
  });
}
function renderSelTags() {
  const box = $('selectedTags'); box.innerHTML = '';
  [...state.tags].forEach(t => {
    const c = chipEl(); c.className = 'chip active'; c.textContent = t + ' ×';
    c.onclick = () => { state.tags.delete(t); update(); }; box.appendChild(c);
  });
}

// ---------- 条件 ----------
const typedFrom = id => [...$(id).value].filter(c => c.trim() && !',、'.includes(c)).map(norm);
const typedChars = () => typedFrom('partInput');

// 読みの検索語：追加済みのタグ＋入力中の文字（ひらがなに正規化、重複なし）
function readingTerms() {
  const all = [...state.readings, $('readingInput').value]
    .map(t => toHira(t.trim().normalize('NFC'))).filter(Boolean);
  return [...new Set(all)];
}

function filterKanji() {
  // 条件は最初に1回だけ用意する（漢字ごとに作り直さない）
  const rqs = readingTerms();
  const need = [...typedChars(), ...state.chars];
  const xneed = [...typedFrom('exInput'), ...state.xchars];   // 含まないパーツ
  const xgs = [...state.xgroups].map(id => groupMap.get(id)).filter(Boolean);
  const gs = [...state.groups].map(id => groupMap.get(id)).filter(Boolean);
  const tagSel = [...state.tags];   // タグは複数選ぶと「どれか」
  const st = state.strokes;   // 画数は、選んだどれか
  return kanjiData.filter(item => {
    if (st.size && !st.has(item.strokes)) return false;
    if (rqs.length) {
      const hit = q => item._rs.has(q) || item.kanji.includes(q);
      if (state.rmode === 'and' ? !rqs.every(hit) : !rqs.some(hit)) return false;
    }
    for (const ch of need) if (!item._parts.has(ch)) return false;
    for (const g of gs) if (!g.members.some(m => item._parts.has(m))) return false; // グループ内はOR
    for (const ch of xneed) if (item._parts.has(ch)) return false;                  // 含まない
    for (const g of xgs) if (g.members.some(m => item._parts.has(m))) return false;
    if (tagSel.length && !tagSel.some(t => item.tags.includes(t))) return false;
    if (state.rads.size && !state.rads.has(item._rad)) return false;   // 部首は、選んだどれか
    return true;
  });
}

// ---------- 表示 ----------
// 並べ替え（同じ値のときは、次の基準で順番を決める）
function sortResults(list) {
  const mode = $('sortSel').value;
  const tagged = it => it.tags.length ? 0 : 1;   // タグあり → タグなし
  const rqs = readingTerms();
  // 読みで検索中は、一致した読みを基準にする
  const yomiOf = it => {
    for (const q of rqs) {
      if (it._rs.has(q)) return q;
    }
    return it._yomi;
  };
  const cmp = {
    sa:    (a, b) => a.strokes - b.strokes || a._rad - b._rad,
    sd:    (a, b) => b.strokes - a.strokes || a._rad - b._rad,
    yomi:  (a, b) => collator.compare(yomiOf(a), yomiOf(b)) || a.strokes - b.strokes,
    bushu: (a, b) => a._rad - b._rad || a.strokes - b.strokes,
  };
  // 標準：タグあり → タグなし、それぞれ部首番号順・同じなら画数順
  if (mode === 'std') return [...list].sort((a, b) => tagged(a) - tagged(b) || cmp.bushu(a, b));
  const c = cmp[mode];
  // 「タグ付きを優先表示」がオンなら、選んだ並べ替えより先にタグの有無で分ける
  return [...list].sort(state.tagFirst ? (a, b) => tagged(a) - tagged(b) || c(a, b) : c);   // 元の並びは変えず、安定して並べ替える
}

function update() {
  renderResults(sortResults(filterKanji()));
  renderReadings();
  renderSelRads();
  renderSelected();
  renderSuggest();
  renderSelTags();
  renderSelStrokes();
  renderSummaries();
  $('tagFirst').classList.toggle('active', state.tagFirst);
  $('tagFirst').setAttribute('aria-pressed', state.tagFirst);
  document.querySelectorAll('.vs-btn').forEach(b => b.setAttribute('aria-pressed', (b.dataset.view === 'compact') === compact));
  syncURL();
  if ($('modal').classList.contains('open')) renderPicker();
  if ($('selModal').classList.contains('open')) renderSel();
}

// 折りたたんだ欄の見出しに、選んでいる条件を短く表示する（表示は textContent なので安全）
function renderSummaries() {
  const put = (id, list) => {
    const items = [...new Set(list.filter(Boolean))], el = $(id);
    el.textContent = items.length ? items.join('・') : '指定なし';
    el.classList.toggle('has', items.length > 0);
  };
  const gname = id => { const g = groupMap.get(id); return g ? g.members[0] + 'グループ' : ''; };
  put('sumParts', [
    ...[...state.groups].map(gname), ...state.chars, ...typedChars(),                   // 含むパーツ
    ...[...state.xgroups].map(id => '除く ' + gname(id)),                                // 含まないパーツ
    ...[...state.xchars, ...typedFrom('exInput')].map(c => '除く ' + c)]);
  put('sumTags', [...state.tags]);
  put('sumReadings', readingTerms());
  put('sumRads', [...state.rads].sort((a, b) => a - b).map(radLabel));
  put('sumStrokes', [...state.strokes].sort((a, b) => a - b).map(n => n + '画'));
}

// 字義（meanings.json）がある字だけ説明を表示する
const meaningOf = it => meanings[it.kanji] || null;

// 漢字カード：左＝漢字（カード全体の縦中央）、右＝タグ／読み（無い種類の行は出さない）／字義
function cardHTML(item) {
  const on = usable(item.readings.on).map(esc).join(' / ');
  const kun = usable(item.readings.kun).map(okuriHTML).join(' / ');
  const na = nanoriOf(item).map(esc).join(' / ');
  const line = (lb, v) => v ? `<div><span class="lb">${lb}</span><span class="rv">${v}</span></div>` : '';
  const m = meaningOf(item);
  const fav = isFav(item.kanji);
  return `<div class="kanji-card">
    <div class="kc-body">
      <div class="kc-char"><div class="kc-charbox"><span class="kanji-char">${esc(item.kanji)}</span>
        <span class="kc-meta">${esc(item.strokes)}画<br>${esc(item.radical.split(/\s+/).join('・'))}</span></div></div>
      <div class="kc-tags">${item.tags.map(t => `<span class="kanji-tag">${esc(t)}</span>`).join('')}</div>
      <div class="kc-btns">
        <button class="copy" data-k="${esc(item.kanji)}" aria-label="この漢字をコピー" title="コピー"><svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="9" y="9" width="12" height="12" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/></svg></button>
        <button class="fav${fav ? ' on' : ''}" data-k="${esc(item.kanji)}" aria-label="お気に入り">${fav ? '★' : '☆'}</button></div>
      <div class="kc-read">${line('音', on)}${line('訓', kun)}${line('名', na)}</div>
      ${m ? `<div class="kc-desc">${esc(m.m)}</div>` : ''}
      ${m && m.place ? `<div class="kanji-place">国・都市の一文字表記：${esc(m.place)}</div>` : ''}
    </div>
  </div>`;
}

// 結果は PAGE 件ずつ表示（全件を一度に作ると重くなるため）
function renderResults(results) {
  closePop(true);
  lastResults = results; shown = 0;
  $('kanjiGrid').classList.toggle('compact', compact);
  $('resultCount').textContent = `検索結果: ${results.length}件`;
  const grid = $('kanjiGrid');
  if (!results.length) {
    grid.innerHTML = '<p class="empty">条件に一致する漢字が見つかりませんでした。</p>';
    $('moreWrap').innerHTML = ''; return;
  }
  grid.innerHTML = '';
  showMore();
}
// コンパクト表示の小さいカード（漢字・画数・部首・☆）
function miniHTML(item) {
  return `<div class="mini-card" data-k="${esc(item.kanji)}"><span class="mini-char">${esc(item.kanji)}</span>
    <span class="mini-meta">${esc(item.strokes)}画・${esc(item.radical.split(/\s+/)[0])}</span>
    <button class="fav${isFav(item.kanji) ? ' on' : ''}" data-k="${esc(item.kanji)}" aria-label="お気に入り">${isFav(item.kanji) ? '★' : '☆'}</button></div>`;
}
function showMore() {
  const next = lastResults.slice(shown, shown + PAGE);
  $('kanjiGrid').insertAdjacentHTML('beforeend', next.map(compact ? miniHTML : cardHTML).join(''));
  shown += next.length;
  const w = $('moreWrap'); w.innerHTML = '';
  if (shown < lastResults.length) {
    const b = document.createElement('button');
    b.className = 'btn'; b.textContent = `さらに表示（${shown} / ${lastResults.length}件）`;
    b.onclick = showMore; w.appendChild(b);
  }
}

// 追加済みの読み（×で解除）と、複数あるときの AND/OR 切り替え
function renderReadings() {
  const box = $('selectedReadings'); box.innerHTML = '';
  state.readings.forEach(t => {
    const c = chipEl(); c.className = 'chip active'; c.textContent = t + ' ×';
    c.onclick = () => { state.readings = state.readings.filter(x => x !== t); update(); };
    box.appendChild(c);
  });
  const m = $('readingMode'); m.innerHTML = '';
  if (readingTerms().length >= 2) {
    const lab = document.createElement('span'); lab.textContent = '複数の読みは:'; m.appendChild(lab);
    [['or', 'どれか含む（OR）'], ['and', 'すべて含む（AND）']].forEach(([v, text]) => {
      m.appendChild(mkChip(text, state.rmode === v, () => { state.rmode = v; update(); }));
    });
  }
}

function renderSelRads() {
  const box = $('selectedRads'); box.innerHTML = '';
  [...state.rads].sort((a, b) => a - b).forEach(n => {
    const c = chipEl(); c.className = 'chip active'; c.textContent = radLabel(n) + ' ×';
    c.onclick = () => { state.rads.delete(n); update(); }; box.appendChild(c);
  });
}

// ---------- タグ・部首・画数の選択画面（共通の形） ----------
const SEL = {
  tag:    { title: 'タグを選ぶ', set: () => state.tags },
  rad:    { title: '部首を選ぶ', set: () => state.rads },
  stroke: { title: '画数を選ぶ', set: () => state.strokes },
};
const toggleIn = (set, k) => () => { set.has(k) ? set.delete(k) : set.add(k); update(); };
function renderSel() {
  const body = $('selBody'); body.innerHTML = '';
  const box = () => { const w = document.createElement('div'); w.className = 'tag-chips'; body.appendChild(w); return w; };
  const note = text => { const n = document.createElement('div'); n.className = 'note'; n.textContent = text; body.appendChild(n); };
  if (selKind === 'tag') {
    note('タップで選択・解除。複数選ぶと、いずれかのタグが付いた漢字を表示します。');
    tagCats.forEach(c => {
      const list = c.tags.filter(t => tagCount.get(t.name));
      if (!list.length) return;
      const h = document.createElement('h3'); h.textContent = c.name; body.appendChild(h);
      const w = box();
      list.forEach(t => {
        const chip = mkChip(`${t.name} (${tagCount.get(t.name)})`, state.tags.has(t.name), toggleIn(state.tags, t.name), 'big');
        chip.title = t.desc || '';
        w.appendChild(chip);
      });
    });
  } else if (selKind === 'rad') {
    // 部首は画数ごとに並べる。0字の部首は出さない
    note('タップで選択・解除。複数選ぶと、いずれかの部首の漢字を表示します。');
    let cur = 0, w = null;
    for (let n = 1; n <= 214; n++) {
      const cnt = radCount.get(n) || 0; if (!cnt) continue;
      const st = radStrokes(n);
      if (st !== cur) {
        cur = st; w = box();
        const h = document.createElement('div'); h.className = 'hdr'; h.textContent = st + '画'; w.appendChild(h);
      }
      w.appendChild(mkChip(`${radLabel(n)} (${cnt})`, state.rads.has(n), toggleIn(state.rads, n), 'big'));
    }
  } else if (selKind === 'stroke') {
    note('タップで選択・解除。複数選ぶと、いずれかの画数の漢字を表示します。');
    const w = box();
    [...strokeCount.keys()].sort((a, b) => a - b).forEach(n =>
      w.appendChild(mkChip(`${n}画 (${strokeCount.get(n)})`, state.strokes.has(n), toggleIn(state.strokes, n), 'big')));
  }
}
function openSel(kind) {
  selKind = kind;
  $('selTitle').textContent = SEL[kind].title;
  openSheet('selModal');
  renderSel();
  $('selBody').scrollTop = 0;
}

// 選択中のパーツ（×で解除）
function renderSelected() {
  const box = $('selectedParts'); box.innerHTML = '';
  const add = (text, fn) => { const c = chipEl(); c.className = 'chip active'; c.textContent = text + ' ×'; c.onclick = fn; box.appendChild(c); };
  state.groups.forEach(id => { const g = groups.find(x => x.id === id); if (g) add(g.label, () => { state.groups.delete(id); update(); }); });
  state.chars.forEach(ch => add(ch, () => { state.chars.delete(ch); viaInput.delete(ch); update(); }));
  // 含まないパーツ（赤）
  const xb = $('selectedEx'); xb.innerHTML = '';
  const xadd = (text, fn) => { const c = chipEl(); c.className = 'chip ex'; c.textContent = '除く: ' + text + ' ×'; c.onclick = fn; xb.appendChild(c); };
  state.xgroups.forEach(id => { const g = groupMap.get(id); if (g) xadd(g.label, () => { state.xgroups.delete(id); update(); }); });
  state.xchars.forEach(ch => xadd(ch, () => { state.xchars.delete(ch); update(); }));
}

// 入力欄にグループ所属の字があれば提案
function renderSuggest() {
  const box = $('suggestBox'); box.innerHTML = '';
  const seen = new Set();
  // 入力中の字、と、Enterで追加したパーツが対象（パーツ選択画面で選んだ形は対象外）
  const targets = [...typedChars(), ...[...state.chars].filter(c => viaInput.has(c))];
  targets.forEach(ch => {
    const g = charToGroup.get(ch);
    if (!g || seen.has(g.id) || state.groups.has(g.id)) return;
    seen.add(g.id);
    const d = document.createElement('div'); d.className = 'suggest';
    const sp = document.createElement('span'); sp.textContent = `「${ch}」は${g.label}にも含められます。`; d.appendChild(sp);
    const b = document.createElement('button'); b.className = 'btn'; b.textContent = 'グループで探す';
    b.onclick = () => {
      $('partInput').value = [...$('partInput').value].filter(c => !g.members.includes(norm(c))).join('');
      g.members.forEach(m => { state.chars.delete(m); viaInput.delete(m); });
      state.groups.add(g.id); update();
    };
    d.appendChild(b); box.appendChild(d);
  });
}

// ---------- パーツ選択画面 ----------
// チップ（押せる小さなボタン）。キーボードでも押せるよう button で作る
function chipEl() { const c = document.createElement('button'); c.type = 'button'; return c; }
function mkChip(text, active, fn, extra) {
  const c = chipEl();
  c.className = 'chip' + (active ? ' active' : '') + (extra ? ' ' + extra : '');
  c.setAttribute('aria-pressed', active ? 'true' : 'false');   // 選択中かどうかを読み上げにも伝える
  c.textContent = text; c.onclick = fn; return c;
}
function renderPicker() {
  const body = $('pickerBody'); body.innerHTML = '';
  const q = $('pickerFilter').value.trim();
  const sv = +$('strokeSel').value, minor = $('showMinor').checked;
  const live = p => partFreq.get(p) || 0;
  const exm = () => $('exMode').checked;
  const flip = (set, other, k) => { if (set.has(k)) set.delete(k); else { set.add(k); other.delete(k); } };   // 含める/除くは同時に選べない
  const toggleChar = x => () => { viaInput.delete(x); exm() ? flip(state.xchars, state.chars, x) : flip(state.chars, state.xchars, x); update(); };
  const toggleGroup = g => () => { exm() ? flip(state.xgroups, state.groups, g.id) : flip(state.groups, state.xgroups, g.id); update(); };
  const exc = x => state.xchars.has(x) ? ' ex' : '';
  const head = (text, note) => {
    const h = document.createElement('h3'); h.textContent = text; body.appendChild(h);
    if (note) { const n = document.createElement('div'); n.className = 'note'; n.textContent = note; body.appendChild(n); }
  };
  const box = () => { const w = document.createElement('div'); w.className = 'tag-chips'; body.appendChild(w); return w; };
  // グループは1グループごとに1行（文字の大きさは他のパーツと同じ）
  const addGroup = (wrap, g) => {
    const row = document.createElement('div'); row.className = 'grp-row';
    row.appendChild(mkChip(g.label, state.groups.has(g.id), toggleGroup(g), 'big' + (state.xgroups.has(g.id) ? ' ex' : '')));
    row.appendChild(mkChip(openGroups.has(g.id) ? '▲閉じる' : '▼形を指定', false, () => { openGroups.has(g.id) ? openGroups.delete(g.id) : openGroups.add(g.id); renderPicker(); }, 'dim'));
    if (openGroups.has(g.id)) {
      const m = document.createElement('div'); m.className = 'exp';
      g.members.filter(x => live(x)).forEach(x => m.appendChild(mkChip(`${x} (${live(x)})`, state.chars.has(x), toggleChar(x), 'big' + exc(x))));
      row.appendChild(m);
    }
    wrap.appendChild(row);
  };
  // ① おすすめ
  if (partsInfo && !q) {
    head('おすすめパーツ', 'タップで選択。形が変わるものは「▼形を指定」で特定の形だけに絞れます。');
    const w = box();
    // グループを先に、単独のパーツをあとに並べる（それぞれ元の順）
    const rec = partsInfo.recommended.map(e => ({ e, g: e.group && groupMap.get(e.group) }));
    rec.filter(x => x.g).forEach(x => addGroup(w, x.g));
    rec.filter(x => !x.g).forEach(x => {
      const p = norm(x.e.forms[0]);
      w.appendChild(mkChip(p, state.chars.has(p), toggleChar(p), 'big' + (live(p) ? '' : ' dim') + exc(p)));
    });
  }
  // ② グループ一覧
  head('形が変わるパーツ（グループ）');
  const gw = box();
  groups.filter(g => !q || g.label.includes(q) || g.members.some(m => q.includes(m))).forEach(g => addGroup(gw, g));
  // ③ すべてのパーツ（画数順）
  head('すべてのパーツ（画数順）', '氵などグループの形は、上のグループから選びます。');
  let list = partsInfo ? partsInfo.parts.map(e => ({ p: norm(e.p), s: e.strokes }))
                       : [...partFreq.keys()].map(p => ({ p, s: 0 }));
  list = list.filter(x => !charToGroup.has(x.p) && live(x.p) >= (minor ? 1 : 2) && (!q || q.includes(x.p)) &&
                          (!sv || (sv === 10 ? x.s >= 10 : x.s === sv)));
  list.sort((a, b) => a.s - b.s || live(b.p) - live(a.p));
  if (!list.length) { const n = document.createElement('div'); n.className = 'note'; n.textContent = '該当するパーツがありません。'; body.appendChild(n); }
  let w = null, cur = -1;
  list.forEach(x => {
    if (x.s !== cur) { cur = x.s; w = box(); if (x.s) { const h = document.createElement('div'); h.className = 'hdr'; h.textContent = x.s + '画'; w.appendChild(h); } }
    w.appendChild(mkChip(`${x.p} (${live(x.p)})`, state.chars.has(x.p), toggleChar(x.p), 'big' + exc(x.p)));
  });
}

// ---------- お気に入り（この端末のブラウザに保存） ----------
const isFav = k => favList.includes(k);
function loadFavs() {
  try {
    const a = JSON.parse(localStorage.getItem('kanjiFavs') || '[]');
    favList = Array.isArray(a) ? a.filter(k => kanjiMap.has(k)) : [];
  } catch (e) { favList = []; }
  loadMemos();
}
// ---------- お気に入りのメモ（この端末のブラウザに保存。お気に入りとは別のキー） ----------
const MEMO_MAX = 100;   // メモの最大文字数
let memos = {};         // 漢字 → メモ
let memoEditing = '';   // いまメモを書いている字（なければ空）
function loadMemos() {
  memos = {};
  try {
    const o = JSON.parse(localStorage.getItem('kanjiFavMemo') || '{}');
    if (o && typeof o === 'object') Object.keys(o).forEach(k => {
      if (isFav(k) && typeof o[k] === 'string' && o[k].trim()) memos[k] = [...o[k]].slice(0, MEMO_MAX).join('');
    });
  } catch (e) { memos = {}; }
}
function saveMemos() {
  try { localStorage.setItem('kanjiFavMemo', JSON.stringify(memos)); } catch (e) { /* 保存できない環境では、開いている間だけ有効 */ }
}
// 1つの字のメモ欄を作る（メモの文字は textContent で表示し、HTMLとしては扱わない）
function renderMemo(box, k) {
  box.textContent = '';
  const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text) e.textContent = text; return e; };
  if (memoEditing === k) {
    const ta = el('textarea', 'memo-input'); ta.maxLength = MEMO_MAX; ta.value = memos[k] || '';
    ta.setAttribute('aria-label', k + 'のメモ');
    const cnt = el('div', 'memo-count');
    const showCount = () => { cnt.textContent = `${[...ta.value].length} / ${MEMO_MAX}文字`; };
    ta.addEventListener('input', showCount); showCount();
    const row = el('div', 'memo-btns');
    const cancel = el('button', 'btn', '取消'); cancel.type = 'button';
    cancel.onclick = () => { memoEditing = ''; renderFavs(); };
    const save = el('button', 'btn primary', '保存'); save.type = 'button';
    save.onclick = () => {
      const v = [...ta.value.trim()].slice(0, MEMO_MAX).join('');
      if (v) memos[k] = v; else delete memos[k];   // 空にしたらメモを消す
      saveMemos(); memoEditing = ''; renderFavs();
    };
    row.append(cancel, save); box.append(ta, cnt, row);
    setTimeout(() => ta.focus(), 0);
  } else if (memos[k]) {
    const b = el('button', 'memo-view'); b.type = 'button'; b.setAttribute('aria-label', k + 'のメモを編集');
    b.append(el('small', '', 'メモ（タップで編集）'), el('span', '', memos[k]));
    b.onclick = () => { memoEditing = k; renderFavs(); };
    box.append(b);
  } else {
    const b = el('button', 'memo-add', '＋ メモを書く'); b.type = 'button';
    b.onclick = () => { memoEditing = k; renderFavs(); };
    box.append(b);
  }
}
function saveFavs() {
  try { localStorage.setItem('kanjiFavs', JSON.stringify(favList)); } catch (e) { /* 保存できない環境では、開いている間だけ有効 */ }
}
function updateFavCount() { $('favCount').textContent = favList.length; }
function toggleFav(k) {
  favList = isFav(k) ? favList.filter(x => x !== k) : [...favList, k];
  if (!isFav(k) && memos[k]) { delete memos[k]; saveMemos(); }   // お気に入りから外したら、その字のメモも消す
  saveFavs(); updateFavCount();
  document.querySelectorAll('.fav').forEach(b => {
    if (b.dataset.k === k) { b.classList.toggle('on', isFav(k)); b.textContent = isFav(k) ? '★' : '☆'; }
  });
  if ($('favModal').classList.contains('open')) renderFavs();
}
function favRowHTML(k) {
  const it = kanjiMap.get(k);
  const on = usable(it.readings.on).map(esc).join(' / ');
  const kun = usable(it.readings.kun).map(okuriHTML).join(' / ');
  const na = nanoriOf(it).map(esc).join(' / ');
  const line = (lb, v) => v ? `<div><span class="lb">${lb}</span><span class="rv">${v}</span></div>` : '';
  const m = meaningOf(it);
  // 左＝漢字と画数・部首、中央＝読み・字義（・メモ）、右＝削除
  return `<div class="fav-row" data-k="${esc(k)}">
    <div class="fav-left"><div class="fav-char">${esc(k)}</div><div class="fav-meta">${esc(it.strokes)}画・${esc(it.radical.split(/\s+/)[0])}</div></div>
    <div class="fav-info"><div class="fav-read">${line('音', on)}${line('訓', kun)}${line('名', na)}</div>
      ${m ? `<div class="fav-desc">${esc(m.m)}</div>` : ''}<div class="fav-memo"></div></div>
    <button class="fav-del" data-del="${esc(k)}">削除</button></div>`;
}
function renderFavs() {
  $('favBody').innerHTML = favList.length ? favList.map(favRowHTML).join('')
    : '<p class="note">まだありません。漢字カードの ☆ をタップすると追加できます。</p>';
  document.querySelectorAll('#favBody .fav-row').forEach(r => renderMemo(r.querySelector('.fav-memo'), r.dataset.k));
}

// ---------- URL連動 ----------
function syncURL() {
  const p = new URLSearchParams();
  const set = (k, v) => { if (v) p.set(k, v); };
  set('r', [...state.readings, $('readingInput').value.trim()].filter(Boolean).join(','));
  set('rm', state.rmode === 'and' ? 'and' : '');
  set('p', $('partInput').value.trim());
  set('g', [...state.groups].join(','));
  set('c', [...state.chars].join(','));
  set('t', [...state.tags].join(','));
  set('b', [...state.rads].join(','));
  set('st', [...state.strokes].sort((a, b) => a - b).join(','));
  set('tp', state.tagFirst ? '1' : '');
  set('xc', [...state.xchars].join(','));
  set('xg', [...state.xgroups].join(','));
  set('s', $('sortSel').value === 'std' ? '' : $('sortSel').value);
  const s = p.toString();
  history.replaceState(history.state, '', s ? '?' + s : location.pathname);   // 画面を開いている印（history.state）は残す
}
function restoreFromURL() {
  const p = new URLSearchParams(location.search);
  $('readingInput').value = '';
  (p.get('r') || '').split(/[,、]/).map(x => x.trim()).filter(Boolean).forEach(x => { if (!state.readings.includes(x)) state.readings.push(x); });
  state.rmode = p.get('rm') === 'and' ? 'and' : 'or';
  $('partInput').value = p.get('p') || '';
  (p.get('g') || '').split(',').filter(Boolean).forEach(x => state.groups.add(x));
  (p.get('c') || '').split(',').filter(Boolean).forEach(x => state.chars.add(x));
  (p.get('t') || '').split(',').filter(Boolean).forEach(x => state.tags.add(x));
  (p.get('st') || '').split(',').map(Number).filter(n => n > 0).forEach(n => state.strokes.add(n));   // 旧URLの sn/sx は無視
  state.tagFirst = p.get('tp') === '1';
  (p.get('xc') || '').split(',').filter(Boolean).forEach(x => state.xchars.add(x));
  (p.get('xg') || '').split(',').filter(Boolean).forEach(x => state.xgroups.add(x));
  (p.get('b') || '').split(',').map(Number).filter(n => n >= 1 && n <= 214).forEach(n => state.rads.add(n));
  const sv = p.get('s'); if ([...$('sortSel').options].some(o => o.value === sv)) $('sortSel').value = sv;
}

// ---------- 下から出る画面（お気に入り・選択画面など）の開閉 ----------
// 開くたびに履歴を1つ積むことで、スマホの「戻る」で上の画面から1枚ずつ閉じられるようにする
const SHEETS = ['modal', 'favModal', 'selModal', 'nameModal', 'cmpModal'];
const sheetStack = [];   // 開いている画面（後から開いたものが最後）
function openSheet(id) {
  $(id).classList.add('open');
  sheetStack.push(id);
  history.pushState({ sheet: id }, '', location.href);
}
function closeSheet(id) {
  if (!$(id).classList.contains('open')) return;
  if (sheetStack[sheetStack.length - 1] === id) { history.back(); return; }   // 積んだ履歴を戻す（閉じる処理は下の popstate で行う）
  const k = sheetStack.indexOf(id); if (k >= 0) sheetStack.splice(k, 1);
  $(id).classList.remove('open'); sheetClosed(id);
}
// 画面を閉じたあとの後片付け
function sheetClosed(id) {
  if (id === 'nameModal') resetName();   // 姓と候補は残さない
}
// 「戻る」が押されたら、いちばん上の画面を閉じる
window.addEventListener('popstate', () => {
  const id = sheetStack.pop();
  if (id) { $(id).classList.remove('open'); sheetClosed(id); }
  syncURL();   // 画面を開いている間に変えた条件を、URLに反映し直す
});

// ---------- 姓と組み合わせて候補を見比べる ----------
// 姓と候補は保存しない（端末にもURLにも残さない）。画面を閉じたら消す。
// 型：名の部分の形。①②③ は「お気に入りの字に置き換える場所」の印。
const MARKS = ['①', '②', '③'];
const KATA_MAX = 5, MARK_MAX = 3;          // 名は5文字まで、印は3つまで
const FONTS = [['min', '明朝'], ['got', 'ゴシック'], ['kyo', '教科書体']];
const NAME = { slots: [], sel: 0, fill: 0, font: 'min' };   // fill：次に入れる印の番号（0なら入れていない）
const charsOf = str => [...str];                            // 1文字ずつに分ける（𠮷 などの字も1文字と数える）
const markNo = c => MARKS.indexOf(c) + 1;                   // ①→1、②→2、③→3、印でない字→0
const marksIn = kata => charsOf(kata).filter(markNo).length;
// 印の番号を、左から ①②③ の順に振り直す
const renumber = kata => { let n = 0; return charsOf(kata).map(c => markNo(c) ? (MARKS[n++] || '') : c).join(''); };
const mk = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text) e.textContent = text; return e; };

function resetName() {
  NAME.slots = [0, 1, 2].map(() => ({ kata: '', chars: {} }));   // chars：印の番号 → 入れた字
  NAME.sel = 0; NAME.fill = 0;
  $('seiInput').value = '';
  $('kataPanel').hidden = true;
}
// 姓＋半角スペース＋名 を el に入れる（文字は textContent 相当で入れ、HTMLとしては扱わない）
function fillName(el, slot) {
  el.textContent = '';
  const sei = $('seiInput').value.trim();
  if (sei) el.append(sei + ' ');
  charsOf(slot.kata).forEach(c => {
    const n = markNo(c);
    if (n && slot.chars[n]) el.append(slot.chars[n]);
    else if (n) el.append(mk('span', 'ph', c));   // まだ字が入っていない印は薄く表示
    else el.append(c);
  });
}
// 教科書体のフォント設定は、使うときに初めて読み込む（ふだんのページを重くしない）
let kyoLoaded = false;
function loadKyoFont() {
  if (kyoLoaded) return; kyoLoaded = true;
  const l = document.createElement('link'); l.rel = 'stylesheet'; l.href = 'fonts/klee-one-v1.css';
  document.head.appendChild(l);
}
function renderName() {
  const editing = !$('kataPanel').hidden;
  const box = $('slots'); box.textContent = '';
  NAME.slots.forEach((sl, i) => {
    const b = mk('button', 'slot' + (i === NAME.sel ? ' sel' : '') + (sl.kata ? '' : ' slot-empty'));
    b.type = 'button'; b.setAttribute('aria-pressed', i === NAME.sel ? 'true' : 'false');
    const v = mk('span', 'slot-name f-' + NAME.font);
    if (sl.kata) fillName(v, sl); else v.textContent = '型を設定してください';
    b.append(v, mk('span', 'slot-no', '候補' + (i + 1)));
    b.onclick = () => {
      if (editing) return;                                  // 型の編集中は選び直さない
      if (NAME.sel !== i) { NAME.sel = i; NAME.fill = 0; }  // 字を入れている途中で別の候補を選んだら、入れるのをやめる（入れた字は残す）
      renderName();
    };
    box.append(b);
  });
  box.classList.toggle('dim', editing);
  $('nameTools').hidden = editing;
  const cur = NAME.slots[NAME.sel], marks = marksIn(cur.kata);
  $('btnFill').disabled = !favList.length || !marks;
  $('btnFill').classList.toggle('primary', NAME.fill > 0);
  $('btnCompare').disabled = !cur.kata;
  document.querySelectorAll('#fontSeg button').forEach(b => b.setAttribute('aria-pressed', b.dataset.font === NAME.font ? 'true' : 'false'));
  $('nameGuide').hidden = favList.length > 0;
  $('fillBox').hidden = !favList.length;
  // お気に入りの字（「字を入れる」の間だけ押せる）
  const t = $('fillTitle'); t.textContent = '';
  if (NAME.fill) t.append(`候補${NAME.sel + 1}の `, mk('b', '', MARKS[NAME.fill - 1]), ' に入れる字をタップ');
  else t.textContent = marks ? '「字を入れる」を押すと、お気に入りの字を ① から順に入れられます' : 'お気に入りの字（型に〇を入れると、ここから入れられます）';
  const chips = $('fillChips'); chips.textContent = '';
  favList.forEach(k => {
    const c = mk('button', 'fill-chip', k); c.type = 'button'; c.disabled = !NAME.fill;
    c.onclick = () => {
      cur.chars[NAME.fill] = k;
      NAME.fill = NAME.fill < marks ? NAME.fill + 1 : 0;   // 最後の印まで入れたら終わり
      renderName();
    };
    chips.append(c);
  });
}
// 型の編集
function openKata() {
  NAME.fill = 0;
  const i = NAME.sel;
  $('kataTitle').textContent = `候補${i + 1}の型`;
  $('kataSei').textContent = $('seiInput').value.trim();
  $('kataInput').value = NAME.slots[i].kata;
  const cp = $('kataCopy'); cp.textContent = '';
  NAME.slots.forEach((sl, j) => {   // ほかの候補の型をコピー（入れた字はコピーしない）
    if (j === i || !sl.kata) return;
    const b = mk('button', 'btn', `候補${j + 1}の型をコピー`); b.type = 'button';
    b.onclick = () => { $('kataInput').value = sl.kata; kataCheck(); };
    cp.append(b);
  });
  $('kataPanel').hidden = false;
  kataCheck(); renderName();
  $('kataInput').focus();
}
function kataCheck() {
  const v = $('kataInput').value.replace(/\s/g, ''), len = charsOf(v).length, m = marksIn(v);
  const ok = len <= KATA_MAX && m <= MARK_MAX;
  $('kataCount').textContent = `名は${KATA_MAX}文字まで・〇は${MARK_MAX}つまで（${len} / ${KATA_MAX}文字、〇 ${m} / ${MARK_MAX}）`;
  $('kataCount').classList.toggle('over', !ok);
  $('kataOk').disabled = !ok;
  $('insMark').disabled = len >= KATA_MAX || m >= MARK_MAX;
}
$('insMark').onclick = () => {
  const el = $('kataInput');
  const st = el.selectionStart == null ? el.value.length : el.selectionStart;
  const en = el.selectionEnd == null ? st : el.selectionEnd;
  el.value = renumber(el.value.slice(0, st) + MARKS[0] + el.value.slice(en));   // カーソルの位置に印を入れ、番号を振り直す
  el.focus(); el.setSelectionRange(st + 1, st + 1);
  kataCheck();
};
$('kataInput').addEventListener('input', kataCheck);
$('kataOk').onclick = () => {
  const sl = NAME.slots[NAME.sel];
  sl.kata = renumber($('kataInput').value.replace(/\s/g, ''));
  const m = marksIn(sl.kata);
  Object.keys(sl.chars).forEach(n => { if (+n > m) delete sl.chars[n]; });   // 入れた字は番号ごとに残す（なくなった番号の字は消す）
  $('kataPanel').hidden = true; renderName();
};
$('kataCancel').onclick = () => { $('kataPanel').hidden = true; renderName(); };
$('btnKata').onclick = openKata;
$('btnFill').onclick = () => { NAME.fill = 1; renderName(); };   // 埋まっていても ① から入れ直す
document.querySelectorAll('#fontSeg button').forEach(b => b.onclick = () => {
  NAME.font = b.dataset.font;
  if (NAME.font === 'kyo') loadKyoFont();
  renderName();
});
$('seiInput').addEventListener('input', renderName);
// 書体を見比べる（3つの書体×縦書き・横書き）
$('btnCompare').onclick = () => {
  const i = NAME.sel, sl = NAME.slots[i]; if (!sl.kata) return;
  loadKyoFont();
  $('cmpTitle').textContent = `書体を見比べる（候補${i + 1}）`;
  ['cmpV', 'cmpH'].forEach(id => {
    const box = $(id); box.textContent = '';
    FONTS.forEach(([f, label]) => {
      const v = mk('span', 'cmp-name f-' + f); fillName(v, sl);
      const c = mk('div', 'cmp-cell'); c.append(mk('span', 'cmp-lb', label), v); box.append(c);
    });
  });
  openSheet('cmpModal');
};
$('openName').onclick = () => { resetName(); renderName(); openSheet('nameModal'); };
$('closeName').onclick = () => closeSheet('nameModal');
$('nameModal').onclick = e => { if (e.target.id === 'nameModal') closeSheet('nameModal'); };
$('closeCmp').onclick = () => closeSheet('cmpModal');
$('cmpModal').onclick = e => { if (e.target.id === 'cmpModal') closeSheet('cmpModal'); };
resetName();

// ---------- イベント ----------
// 入力のたびに検索せず、入力が止まってから検索する。変換中（IME）は待つ。
let compEndAt = 0;
function schedule(fn, ms) { clearTimeout(timer); timer = setTimeout(fn, ms); }
['readingInput', 'partInput', 'exInput'].forEach(id => {
  const el = $(id);
  el.addEventListener('compositionstart', () => { composing = true; clearTimeout(timer); });
  el.addEventListener('compositionend', () => { composing = false; compEndAt = Date.now(); schedule(update, 150); });
  el.addEventListener('input', e => { if (composing || e.isComposing) return; schedule(update, 150); });
});

// Enterで入力欄の文字をタグにする（変換を確定するEnterは除く）
function onEnter(id, fn) {
  $(id).addEventListener('keydown', e => {
    if (e.key !== 'Enter') return;
    if (composing || e.isComposing || e.keyCode === 229 || Date.now() - compEndAt < 60) return;
    e.preventDefault(); clearTimeout(timer); fn();
  });
}
onEnter('readingInput', () => {
  $('readingInput').value.trim().normalize('NFC').split(/[\s,、]+/).filter(Boolean).forEach(t => {
    if (!state.readings.some(x => toHira(x) === toHira(t))) state.readings.push(t);
  });
  $('readingInput').value = ''; update();
});
onEnter('partInput', () => {
  typedChars().forEach(ch => { state.chars.add(ch); viaInput.add(ch); state.xchars.delete(ch); });
  $('partInput').value = ''; update();
});
onEnter('exInput', () => {
  typedFrom('exInput').forEach(ch => { state.xchars.add(ch); state.chars.delete(ch); viaInput.delete(ch); });
  $('exInput').value = ''; update();
});
$('exMode').addEventListener('change', renderPicker);
$('tagFirst').onclick = () => { state.tagFirst = !state.tagFirst; update(); };
// 表示の切り替え：押したほうの表示にする（今と同じほうを押しても何もしない）
document.querySelectorAll('.vs-btn').forEach(b => b.onclick = () => {
  const c = b.dataset.view === 'compact';
  if (c === compact) return;
  compact = c;
  try { localStorage.setItem('kanjiView', compact ? 'compact' : 'detail'); } catch (e) {}
  update();
});

// ---------- コンパクト表示：タップで横に広げる ----------
let pop = null, popSrc = null, pressAt = 0, pressX = 0, pressY = 0, scrollAt = 0;
const DUR = 300;   // アニメーションの長さ（ミリ秒）
// 小さいカードの位置（グリッド基準）
function rectIn(el) {
  const g = $('kanjiGrid').getBoundingClientRect(), r = el.getBoundingClientRect();
  return { left: r.left - g.left, top: r.top - g.top, width: r.width, height: r.height };
}
function openPop(mini) {
  const item = kanjiMap.get(mini.dataset.k); if (!item) return;
  const grid = $('kanjiGrid'), from = rectIn(mini);
  const el = document.createElement('div');
  el.innerHTML = cardHTML(item);
  const card = el.firstElementChild;
  card.classList.add('kanji-pop');
  // 広げたあとの高さを先に測る
  card.style.cssText = `left:0;top:${from.top}px;width:${grid.clientWidth}px;visibility:hidden;transition:none`;
  grid.appendChild(card);
  const fullH = card.scrollHeight;
  // 小さいカードの位置から始める
  card.style.cssText = `left:${from.left}px;top:${from.top}px;width:${from.width}px;height:${from.height}px;transition:none`;
  card.getBoundingClientRect();   // 位置を確定させてからアニメーション
  card.style.transition = '';
  card.style.left = '0px'; card.style.width = grid.clientWidth + 'px'; card.style.height = fullH + 'px';
  setTimeout(() => { if (pop === card) card.style.height = 'auto'; }, DUR + 20);
  mini.classList.add('sel');
  pop = card; popSrc = mini; scrollAt = window.scrollY;
}
function closePop(instant) {
  if (!pop) return;
  const card = pop, mini = popSrc; pop = null; popSrc = null;
  if (mini) mini.classList.remove('sel');
  if (instant || !mini || !mini.isConnected) { card.remove(); return; }
  const to = rectIn(mini);
  card.style.height = card.offsetHeight + 'px';
  card.getBoundingClientRect();
  card.style.left = to.left + 'px'; card.style.width = to.width + 'px'; card.style.height = to.height + 'px';
  setTimeout(() => card.remove(), DUR + 20);
}
// 長押し（コピーのため）は反応しない。短いタップだけを扱う
document.addEventListener('pointerdown', e => { pressAt = Date.now(); pressX = e.clientX; pressY = e.clientY; }, true);
document.addEventListener('click', e => {
  const isTap = Date.now() - pressAt < 500 && Math.abs(e.clientX - pressX) < 10 && Math.abs(e.clientY - pressY) < 10;
  if (!isTap) return;
  if (e.target.closest('.fav, .copy')) return;               // ☆はお気に入りだけ・コピーはコピーだけ（カードは閉じない）
  const selText = String(window.getSelection && window.getSelection());
  if (pop && e.target.closest('.kanji-pop') && selText) return; // 文字を選んでいる間は閉じない
  const mini = e.target.closest('.mini-card');
  if (pop) { const same = mini && mini === popSrc; closePop(); if (same || !mini) return; }
  if (mini) openPop(mini);
}, true);
// スワイプ（スクロール）したら閉じる
window.addEventListener('scroll', () => { if (pop && Math.abs(window.scrollY - scrollAt) > 12) closePop(); }, { passive: true });
window.addEventListener('resize', () => closePop(true));

// ---------- ページの先頭へ戻るボタン ----------
// 1画面分より下までスクロールしたら表示する
function updateToTop() { $('toTop').hidden = window.scrollY < window.innerHeight; }
window.addEventListener('scroll', updateToTop, { passive: true });
$('toTop').onclick = () => {
  const still = window.matchMedia('(prefers-reduced-motion: reduce)').matches;   // 動きを減らす設定なら一瞬で移動
  window.scrollTo({ top: 0, behavior: still ? 'auto' : 'smooth' });
};

// お気に入り
$('kanjiGrid').addEventListener('click', e => { const b = e.target.closest('.fav'); if (b) toggleFav(b.dataset.k); });
$('openFav').onclick = () => { memoEditing = ''; renderFavs(); openSheet('favModal'); };
$('closeFav').onclick = () => closeSheet('favModal');
$('favModal').onclick = e => { if (e.target.id === 'favModal') closeSheet('favModal'); };
$('favBody').addEventListener('click', e => { const b = e.target.closest('[data-del]'); if (b) toggleFav(b.dataset.del); });
$('favClear').onclick = () => { if (favList.length && confirm('お気に入りをすべて削除しますか？')) { favList = []; memos = {}; saveFavs(); saveMemos(); updateFavCount(); renderFavs(); update(); } };
// クリップボードにコピー（使えない環境は execCommand で代用）
async function copyText(text) {
  try { await navigator.clipboard.writeText(text); return true; }
  catch (e) {
    const ta = document.createElement('textarea'); ta.value = text; ta.setAttribute('readonly', '');
    ta.style.position = 'fixed'; ta.style.opacity = '0'; document.body.appendChild(ta);
    ta.select(); ta.setSelectionRange(0, text.length);
    let ok = false; try { ok = document.execCommand('copy'); } catch (_) {} ta.remove(); return ok;
  }
}
// カードのコピーボタン：漢字1字をコピーして「コピーしました」を少し表示
$('kanjiGrid').addEventListener('click', async e => {
  const b = e.target.closest('.copy'); if (!b) return;
  const ok = await copyText(b.dataset.k);
  const head = b.closest('.kc-btns');
  head.querySelectorAll('.copy-msg').forEach(x => x.remove());
  const msg = document.createElement('span'); msg.className = 'copy-msg';
  msg.textContent = ok ? 'コピーしました' : 'コピーできませんでした';
  head.appendChild(msg);
  setTimeout(() => msg.remove(), 1500);
});
$('favCopy').onclick = async () => {
  const text = favList.join('、'); if (!text) return;
  const ok = await copyText(text);
  $('favMsg').textContent = ok ? 'コピーしました' : 'コピーできませんでした';
  setTimeout(() => { $('favMsg').textContent = ''; }, 2000);
};
$('pickerFilter').addEventListener('input', () => schedule(renderPicker, 150));
$('sortSel').addEventListener('change', update);
$('strokeSel').addEventListener('change', renderPicker);
$('showMinor').addEventListener('change', renderPicker);
$('openPicker').onclick = () => { openSheet('modal'); renderPicker(); };
$('closePicker').onclick = () => closeSheet('modal');
$('modal').onclick = e => { if (e.target.id === 'modal') closeSheet('modal'); };
// タグ・部首・画数の選択画面
$('openTags').onclick = () => openSel('tag');
$('openRads').onclick = () => openSel('rad');
$('openStrokes').onclick = () => openSel('stroke');
$('selClose').onclick = () => closeSheet('selModal');
$('selModal').onclick = e => { if (e.target.id === 'selModal') closeSheet('selModal'); };
$('selClear').onclick = () => { if (SEL[selKind]) { SEL[selKind].set().clear(); update(); } };
$('clearAll').onclick = () => {
  $('readingInput').value = ''; $('partInput').value = ''; $('exInput').value = '';
  state.strokes.clear(); state.tagFirst = false;
  state.groups.clear(); state.chars.clear(); state.tags.clear(); state.rads.clear(); state.xchars.clear(); state.xgroups.clear(); viaInput.clear();
  state.readings = []; state.rmode = 'or'; update();
};

loadData();
