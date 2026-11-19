/*************************************************************************
 * 麻雀 実戦何切るトレーナー 厳密解析＆10大戦術難問エンジン (engine.js)
 * - シャンテン数厳密検証（0 / 1 / 2 / 3シャンテン）＋2手先読み評価
 * - 高打点飽和対応・多面張枚数最優先ソルバー＆三暗刻/対々和/符計算対応
 * - 数値大小関係に完全準拠した1対1比較解説ジェネレーター
 *************************************************************************/

const isYaochu = (idx) => idx >= 27 || (idx % 9 === 0) || (idx % 9 === 8);
const pickRandom = (arr) => arr[Math.floor(Math.random() * arr.length)];

function getActualDoraIdx(ind) {
  if (ind < 27) return Math.floor(ind / 9) * 9 + ((ind % 9 + 1) % 9);
  if (ind <= 30) return 27 + ((ind - 27 + 1) % 4);
  return 31 + ((ind - 31 + 1) % 3);
}

function getIndicatorForDora(doraIdx) {
  if (doraIdx < 27) return Math.floor(doraIdx / 9) * 9 + ((doraIdx % 9 + 8) % 9);
  if (doraIdx <= 30) return 27 + ((doraIdx - 27 + 3) % 4);
  return 31 + ((doraIdx - 31 + 2) % 3);
}

function renderMiniTileInline(tileIdx, sizeClass = 'w-[18px] sm:w-[20px]') {
  return `<span class="inline-block ${sizeClass} aspect-[100/138] align-middle" title="${TILE_NAMES_JA[tileIdx]}">${renderTileSVG(tileIdx)}</span>`;
}

function calcEffectivePoints(pts, isDealer) {
  const mangan = isDealer ? 12000 : 8000;
  if (pts <= mangan) return pts;
  return Math.round(mangan + (pts - mangan) * 0.05);
}

/* 1. スート別高速シャンテン数計算（4面子1雀頭） */
function solveSuitMaxBlocks(counts, offset) {
  const bestT = [-1, -1, -1, -1, -1];
  function dfs(pos, m, t) {
    while (pos < 9 && counts[offset + pos] === 0) pos++;
    if (pos >= 9) {
      if (t > bestT[m]) bestT[m] = t;
      return;
    }
    const idx = offset + pos, c = counts[idx];
    if (c >= 3 && m < 4) { counts[idx] -= 3; dfs(pos, m + 1, t); counts[idx] += 3; }
    if (pos <= 6 && m < 4 && counts[idx + 1] > 0 && counts[idx + 2] > 0) {
      counts[idx]--; counts[idx + 1]--; counts[idx + 2]--;
      dfs(pos, m + 1, t);
      counts[idx]++; counts[idx + 1]++; counts[idx + 2]++;
    }
    if (c >= 2 && m + t < 4) { counts[idx] -= 2; dfs(pos, m, t + 1); counts[idx] += 2; }
    if (pos <= 7 && m + t < 4 && counts[idx + 1] > 0) {
      counts[idx]--; counts[idx + 1]--; dfs(pos, m, t + 1); counts[idx]++; counts[idx + 1]++;
    }
    if (pos <= 6 && m + t < 4 && counts[idx + 2] > 0) {
      counts[idx]--; counts[idx + 2]--; dfs(pos, m, t + 1); counts[idx]++; counts[idx + 2]++;
    }
    dfs(pos + 1, m, t);
  }
  dfs(0, 0, 0);
  return bestT;
}

function evalConfigShanten(counts, hasPair) {
  const s0 = solveSuitMaxBlocks(counts, 0);
  const s1 = solveSuitMaxBlocks(counts, 9);
  const s2 = solveSuitMaxBlocks(counts, 18);
  let zM = 0, zT = 0;
  for (let i = 27; i < 34; i++) {
    if (counts[i] >= 3) zM++;
    else if (counts[i] === 2) zT++;
  }
  let minSh = 8;
  for (let m0 = 0; m0 <= 4; m0++) {
    if (s0[m0] < 0) continue;
    for (let m1 = 0; m1 <= 4 - m0; m1++) {
      if (s1[m1] < 0) continue;
      for (let m2 = 0; m2 <= 4 - m0 - m1; m2++) {
        if (s2[m2] < 0) continue;
        const totalM = Math.min(4, m0 + m1 + m2 + zM);
        const effT = Math.min(4 - totalM, s0[m0] + s1[m1] + s2[m2] + zT);
        const sh = 8 - totalM * 2 - effT - (hasPair ? 1 : 0);
        if (sh < minSh) minSh = sh;
      }
    }
  }
  return minSh;
}

function calcStandardShantenFromCounts(counts) {
  let minSh = evalConfigShanten(counts, false);
  for (let i = 0; i < 34; i++) {
    if (counts[i] >= 2) {
      counts[i] -= 2;
      const sh = evalConfigShanten(counts, true);
      if (sh < minSh) minSh = sh;
      counts[i] += 2;
    }
  }
  return minSh;
}

/* 2. 14枚アガリ役・符・打点計算（完全面子分解） */
function evaluateWinning14(counts14, winTile, roundWind, seatWind, doraIdx) {
  const doraCount = counts14[doraIdx];
  const allTiles = [];
  for (let i = 0; i < 34; i++) for (let k = 0; k < counts14[i]; k++) allTiles.push(i);
  let best = null;

  function extract(c, start, cur, out) {
    let first = -1;
    for (let i = start; i < 34; i++) if (c[i] > 0) { first = i; break; }
    if (first === -1) {
      if (cur.length === 4) out.push(cur.map(m => ({ kind: m.kind, tiles: [...m.tiles] })));
      return;
    }
    if (c[first] >= 3) {
      c[first] -= 3; cur.push({ kind: 'koutsu', tiles: [first, first, first] });
      extract(c, first, cur, out); cur.pop(); c[first] += 3;
    }
    if (first < 27 && (first % 9) <= 6 && c[first + 1] > 0 && c[first + 2] > 0) {
      c[first]--; c[first + 1]--; c[first + 2]--;
      cur.push({ kind: 'shuntsu', tiles: [first, first + 1, first + 2] });
      extract(c, first, cur, out); cur.pop();
      c[first]++; c[first + 1]++; c[first + 2]++;
    }
  }

  for (let jIdx = 0; jIdx < 34; jIdx++) {
    if (counts14[jIdx] < 2) continue;
    counts14[jIdx] -= 2;
    const parts = [];
    extract(counts14, 0, [], parts);
    counts14[jIdx] += 2;

    for (const mentsu of parts) {
      const waits = [];
      if (jIdx === winTile) waits.push({ waitType: 'tanki', mIdx: -1 });
      mentsu.forEach((m, mIdx) => {
        if (!m.tiles.includes(winTile)) return;
        if (m.kind === 'koutsu') waits.push({ waitType: 'shanpon', mIdx });
        else {
          const a = m.tiles[0];
          if (winTile === a + 1) waits.push({ waitType: 'kanchan', mIdx });
          else if ((winTile === a + 2 && a % 9 === 0) || (winTile === a && a % 9 === 6)) waits.push({ waitType: 'penchan', mIdx });
          else waits.push({ waitType: 'ryanmen', mIdx });
        }
      });

      for (const wc of waits) {
        const yaku = [];
        const allShuntsu = mentsu.every(m => m.kind === 'shuntsu');
        const isYakuhaiPair = jIdx >= 31 || jIdx === roundWind || jIdx === seatWind;
        const isPinfu = allShuntsu && !isYakuhaiPair && wc.waitType === 'ryanmen';
        if (isPinfu) yaku.push({ name: '平和', han: 1 });
        if (allTiles.every(t => !isYaochu(t))) yaku.push({ name: '断幺九', han: 1 });

        mentsu.forEach(m => {
          if (m.kind === 'koutsu') {
            const t = m.tiles[0];
            if (t === roundWind && t === seatWind) yaku.push({ name: `ダブ${TILE_NAMES_JA[t]}`, han: 2 });
            else if (t === roundWind || t === seatWind) yaku.push({ name: `役牌 ${TILE_NAMES_JA[t]}`, han: 1 });
            if (t >= 31) yaku.push({ name: `役牌 ${TILE_NAMES_JA[t]}`, han: 1 });
          }
        });

        const sKeys = mentsu.filter(m => m.kind === 'shuntsu').map(m => m.tiles[0]);
        const kMap = {};
        sKeys.forEach(k => { kMap[k] = (kMap[k] || 0) + 1; });
        const pairSeqs = Object.values(kMap).reduce((s, v) => s + Math.floor(v / 2), 0);
        if (pairSeqs === 2) yaku.push({ name: '二盃口', han: 3 });
        else if (pairSeqs === 1) yaku.push({ name: '一盃口', han: 1 });

        for (let pos = 0; pos <= 6; pos++) {
          if (sKeys.includes(pos) && sKeys.includes(9 + pos) && sKeys.includes(18 + pos)) {
            yaku.push({ name: '三色同順', han: 2 }); break;
          }
        }
        for (const sb of [0, 9, 18]) {
          if (sKeys.includes(sb) && sKeys.includes(sb + 3) && sKeys.includes(sb + 6)) {
            yaku.push({ name: '一気通貫', han: 2 }); break;
          }
        }

        const koutsuCount = mentsu.filter(m => m.kind === 'koutsu').length;
        if (koutsuCount === 4) yaku.push({ name: '対々和', han: 2 });
        const ankouRonCount = mentsu.filter((m, idx) => m.kind === 'koutsu' && idx !== wc.mIdx).length;
        if (ankouRonCount >= 3) yaku.push({ name: '三暗刻', han: 2 });

        const hasShuntsu = mentsu.some(m => m.kind === 'shuntsu');
        const allYao = mentsu.every(m => m.tiles.some(t => isYaochu(t))) && isYaochu(jIdx);
        const hasHonor = allTiles.some(t => t >= 27);
        if (allYao && hasShuntsu) yaku.push({ name: hasHonor ? '混全帯幺九' : '純全帯幺九', han: hasHonor ? 2 : 3 });

        const suits = new Set();
        allTiles.forEach(t => { if (t < 27) suits.add(Math.floor(t / 9)); });
        if (suits.size === 1) yaku.push({ name: hasHonor ? '混一色' : '清一色', han: hasHonor ? 3 : 6 });

        const yakuHan = yaku.reduce((s, y) => s + y.han, 0);

        let rawFu = 30;
        if (!isPinfu) {
          mentsu.forEach((m, idx) => {
            if (m.kind === 'koutsu') {
              const yao = isYaochu(m.tiles[0]);
              const isMinkou = idx === wc.mIdx;
              rawFu += isMinkou ? (yao ? 4 : 2) : (yao ? 8 : 4);
            }
          });
          if (isYakuhaiPair) rawFu += 2;
          if (wc.waitType === 'kanchan' || wc.waitType === 'penchan' || wc.waitType === 'tanki') rawFu += 2;
        }
        const fu = isPinfu ? 30 : Math.max(30, Math.ceil(rawFu / 10) * 10);
        const totalHan = 1 + yakuHan + doraCount;
        const isDealer = seatWind === 27;
        const isKiriageMangan = (totalHan === 3 && fu === 60) || (totalHan === 4 && fu === 30);

        let base = fu * Math.pow(2, totalHan + 2);
        if (totalHan >= 13) base = 8000;
        else if (totalHan >= 11) base = 6000;
        else if (totalHan >= 8) base = 4000;
        else if (totalHan >= 6) base = 3000;
        else if (totalHan >= 5 || base >= 2000 || isKiriageMangan) base = 2000;
        const ronPoints = Math.ceil((base * (isDealer ? 6 : 4)) / 100) * 100;

        const yakuNames = yaku.map(y => y.name);
        if (doraCount > 0) yakuNames.push(`ドラ${doraCount}`);

        if (!best || ronPoints > best.ronPoints || (ronPoints === best.ronPoints && yakuHan > best.yakuHan)) {
          best = { ronPoints, yakuHan, doraCount, yakuNames, isPinfu, fu };
        }
      }
    }
  }
  return best;
}

function evaluate13Tenpai(counts13, visibleCounts, roundWind, seatWind, doraIdx) {
  const isDealer = seatWind === 27;
  const waits = [];
  let totalWaitTiles = 0, maxRonPoints = 0, weightedPts = 0, weightedEffPts = 0;
  const yakuFreq = {};

  for (let t = 0; t < 34; t++) {
    if (counts13[t] >= 4) continue;
    const rem = Math.max(0, 4 - visibleCounts[t]);
    if (rem <= 0) continue;

    counts13[t]++;
    const w = evaluateWinning14(counts13, t, roundWind, seatWind, doraIdx);
    counts13[t]--;
    if (w) {
      waits.push({ tile: t, rem, ...w });
      totalWaitTiles += rem;
      if (w.ronPoints > maxRonPoints) maxRonPoints = w.ronPoints;
      weightedPts += w.ronPoints * rem;
      weightedEffPts += calcEffectivePoints(w.ronPoints, isDealer) * rem;
      w.yakuNames.forEach(yn => { yakuFreq[yn] = (yakuFreq[yn] || 0) + rem; });
    }
  }
  if (waits.length === 0 || totalWaitTiles === 0) return null;
  const sortedYaku = Object.keys(yakuFreq).sort((a, b) => yakuFreq[b] - yakuFreq[a]);
  return {
    waits,
    totalWaitTiles,
    waitTypesCount: waits.length,
    maxRonPoints,
    avgPoints: Math.round(weightedPts / totalWaitTiles),
    avgEffPoints: Math.round(weightedEffPts / totalWaitTiles),
    yakuSummary: sortedYaku
  };
}

/* 3. 2〜3シャンテン専用：ブロック分解に基づく厳密な手役・好形評価器 */
function hasValidIttsuBlocks(counts13, suitOffset) {
  const c = counts13.slice(suitOffset, suitOffset + 9);
  const seg1 = (c[0] > 0 ? 1 : 0) + (c[1] > 0 ? 1 : 0) + (c[2] > 0 ? 1 : 0);
  const seg2 = (c[3] > 0 ? 1 : 0) + (c[4] > 0 ? 1 : 0) + (c[5] > 0 ? 1 : 0);
  const seg3 = (c[6] > 0 ? 1 : 0) + (c[7] > 0 ? 1 : 0) + (c[8] > 0 ? 1 : 0);
  return seg1 >= 2 && seg2 >= 2 && seg3 >= 2 && (seg1 + seg2 + seg3 >= 7);
}

function hasValidSanshokuBlocks(counts13) {
  for (let pos = 0; pos <= 6; pos++) {
    const m = (counts13[pos] > 0 ? 1 : 0) + (counts13[pos + 1] > 0 ? 1 : 0) + (counts13[pos + 2] > 0 ? 1 : 0);
    const p = (counts13[9 + pos] > 0 ? 1 : 0) + (counts13[9 + pos + 1] > 0 ? 1 : 0) + (counts13[9 + pos + 2] > 0 ? 1 : 0);
    const s = (counts13[18 + pos] > 0 ? 1 : 0) + (counts13[18 + pos + 1] > 0 ? 1 : 0) + (counts13[18 + pos + 2] > 0 ? 1 : 0);
    if (m >= 2 && p >= 2 && s >= 2 && (m + p + s >= 7)) return true;
  }
  return false;
}

function evaluate2And3ShantenStructure(counts13, doraIdx) {
  let score = 0;
  const tags = [];
  const doraCnt = counts13[doraIdx];

  const suitCounts = [0, 0, 0];
  let honorCnt = 0, yaoCnt = 0;
  for (let i = 0; i < 34; i++) {
    const c = counts13[i];
    if (!c) continue;
    if (isYaochu(i)) yaoCnt += c;
    if (i < 27) suitCounts[Math.floor(i / 9)] += c;
    else honorCnt += c;
  }

  const maxSuit = Math.max(...suitCounts);
  if (maxSuit + honorCnt === 13) {
    score += honorCnt === 0 ? 160 : 110;
    tags.push(honorCnt === 0 ? '清一色' : '混一色');
  }

  if (yaoCnt === 0) {
    score += 65;
    tags.push('断幺九');
  }

  if (hasValidSanshokuBlocks(counts13)) {
    score += 75;
    tags.push('三色同順');
  }

  if (hasValidIttsuBlocks(counts13, 0) || hasValidIttsuBlocks(counts13, 9) || hasValidIttsuBlocks(counts13, 18)) {
    score += 70;
    tags.push('一気通貫');
  }

  let hasGoodComplex = false;
  for (let s = 0; s < 3; s++) {
    const b = s * 9;
    for (let p = 0; p <= 6; p++) {
      if (counts13[b + p] >= 2 && counts13[b + p + 1] >= 2 && counts13[b + p + 2] >= 2) {
        score += 45;
        if (!tags.includes('一盃口')) tags.push('一盃口');
      }
    }
    for (let p = 1; p <= 4; p++) {
      if (counts13[b + p] > 0 && counts13[b + p + 1] > 0 && counts13[b + p + 2] > 0 && counts13[b + p + 3] > 0) {
        score += 24; hasGoodComplex = true;
      }
    }
    for (let p = 1; p <= 5; p++) {
      if (counts13[b + p] > 0 && counts13[b + p + 1] >= 2 && counts13[b + p + 2] > 0) {
        score += 22; hasGoodComplex = true;
      }
    }
    for (let p = 1; p <= 6; p++) {
      if (counts13[b + p] > 0 && counts13[b + p + 1] > 0) score += 12;
    }
    if (counts13[b] > 0 && counts13[b + 1] > 0 && counts13[b + 2] === 0) score -= 24;
    if (counts13[b + 8] > 0 && counts13[b + 7] > 0 && counts13[b + 6] === 0) score -= 24;
  }

  if (doraCnt > 0) {
    score += doraCnt * 36;
    tags.push(`ドラ${doraCnt}`);
  }
  if (tags.length === 0) tags.push(hasGoodComplex ? '好形連続形' : '好形変化');

  return { shapeScore: score, tags };
}

/* 4. 14枚手牌の全打牌候補ソルバー */
function analyze14Hand(hand14, roundWind, seatWind, doraInd, category = 'auto') {
  const doraIdx = getActualDoraIdx(doraInd);
  const fullCounts = new Array(34).fill(0);
  hand14.forEach(t => fullCounts[t]++);
  const visible = [...fullCounts];
  visible[doraInd]++;

  const suitTotals = [0, 0, 0];
  let honorTotal = 0;
  hand14.forEach(t => { if (t < 27) suitTotals[Math.floor(t / 9)]++; else honorTotal++; });
  const isFlushHand = (Math.max(...suitTotals) + honorTotal >= 13) || category.startsWith('menchin');

  const currentShanten = calcStandardShantenFromCounts([...fullCounts]);
  const uniqueDiscards = Array.from(new Set(hand14)).sort((a, b) => a - b);
  const candidates = [];

  for (const discardTile of uniqueDiscards) {
    const counts13 = [...fullCounts];
    counts13[discardTile]--;
    const shAfter = calcStandardShantenFromCounts([...counts13]);
    if (shAfter > currentShanten) continue;

    if (currentShanten === 0) {
      const tp = evaluate13Tenpai(counts13, visible, roundWind, seatWind, doraIdx);
      if (!tp) continue;
      const scoreMetric = isFlushHand
        ? tp.totalWaitTiles * 100000 + tp.waitTypesCount * 1000 + Math.round(tp.avgEffPoints / 100)
        : tp.totalWaitTiles * 100000 + tp.avgEffPoints + tp.waitTypesCount * 100;

      candidates.push({
        discardTile,
        ukeireCount: tp.totalWaitTiles,
        ukeireTypes: tp.waitTypesCount,
        ukeireList: tp.waits.map(w => ({ tile: w.tile, rem: w.rem, subLabel: `${w.ronPoints.toLocaleString()}点` })),
        maxPoints: tp.maxRonPoints,
        avgPoints: tp.avgPoints,
        nextStageAvgWidth: tp.totalWaitTiles,
        yakuSummary: tp.yakuSummary.length ? tp.yakuSummary : ['リーチ'],
        transitions: [],
        scoreMetric
      });
    } else if (currentShanten === 1) {
      const ukeireList = [], transitions = [];
      let totalUkeire = 0, bestMaxPts = 0, weightedWaits = 0, weightedPts = 0, weightedScore = 0;
      const yakuWeightMap = {};

      for (let draw = 0; draw < 34; draw++) {
        if (counts13[draw] >= 4) continue;
        const rem = Math.max(0, 4 - visible[draw]);
        if (rem <= 0) continue;

        counts13[draw]++;
        if (calcStandardShantenFromCounts([...counts13]) === 0) {
          let bestTp = null, bestNextDisc = -1;
          for (let nd = 0; nd < 34; nd++) {
            if (!counts13[nd]) continue;
            counts13[nd]--;
            if (calcStandardShantenFromCounts([...counts13]) === 0) {
              const visNext = [...visible]; visNext[draw]++;
              const tp = evaluate13Tenpai(counts13, visNext, roundWind, seatWind, doraIdx);
              if (tp) {
                const rank = isFlushHand
                  ? tp.totalWaitTiles * 10000 + tp.waitTypesCount * 200 + tp.avgEffPoints * 0.1
                  : tp.totalWaitTiles * 700 + tp.avgEffPoints * 1.15;
                if (!bestTp || rank > bestTp.rank) { bestTp = { ...tp, rank }; bestNextDisc = nd; }
              }
            }
            counts13[nd]++;
          }
          if (bestTp) {
            ukeireList.push({ tile: draw, rem, subLabel: `待${bestTp.totalWaitTiles}枚` });
            totalUkeire += rem;
            weightedWaits += rem * bestTp.totalWaitTiles;
            weightedPts += rem * bestTp.avgPoints;
            if (bestTp.maxRonPoints > bestMaxPts) bestMaxPts = bestTp.maxRonPoints;

            const waitFactor = Math.min(14, Math.max(2, bestTp.totalWaitTiles));
            weightedScore += rem * (waitFactor * 480 + bestTp.avgEffPoints * 0.85);

            bestTp.yakuSummary.forEach(yn => {
              yakuWeightMap[yn] = (yakuWeightMap[yn] || 0) + rem;
            });

            const waitMiniIcons = bestTp.waits.map(w => renderMiniTileInline(w.tile, 'w-[15px] sm:w-[17px]')).join('');
            transitions.push({
              drawTile: draw,
              rem,
              nextDiscard: bestNextDisc,
              detailHtml: `<span class="inline-flex items-center gap-0.5 align-middle">${waitMiniIcons}</span> <span class="align-middle">待ち (${bestTp.totalWaitTiles}枚)</span>`,
              badgeText: bestTp.yakuSummary.join('・') || 'リーチのみ',
              sortKey: bestTp.totalWaitTiles * 100000 + bestTp.avgEffPoints
            });
          }
        }
        counts13[draw]--;
      }

      if (!ukeireList.length) continue;
      transitions.sort((a, b) => b.sortKey - a.sortKey);
      const nextStageAvgWidth = +(weightedWaits / totalUkeire).toFixed(1);
      const avgPoints = Math.round(weightedPts / totalUkeire);

      const validYaku = Object.keys(yakuWeightMap)
        .filter(yn => yakuWeightMap[yn] >= Math.min(4, totalUkeire * 0.25))
        .sort((a, b) => yakuWeightMap[b] - yakuWeightMap[a])
        .slice(0, 4);

      const scoreMetric = isFlushHand
        ? totalUkeire * 10000 + Math.round(weightedWaits * 50)
        : Math.round(weightedScore + totalUkeire * 380);

      candidates.push({
        discardTile,
        ukeireCount: totalUkeire,
        ukeireTypes: ukeireList.length,
        ukeireList,
        maxPoints: bestMaxPts,
        avgPoints,
        nextStageAvgWidth,
        yakuSummary: validYaku.length ? validYaku : ['リーチ'],
        transitions,
        scoreMetric
      });
    } else {
      const struct = evaluate2And3ShantenStructure(counts13, doraIdx);
      const ukeireList = [], transitions = [];
      let totalUkeire = 0, weightedNextUkeire = 0, weightedNextRank = 0;
      const tagWeightMap = {};
      struct.tags.forEach(t => { tagWeightMap[t] = 10; });

      for (let draw = 0; draw < 34; draw++) {
        if (counts13[draw] >= 4) continue;
        const rem = Math.max(0, 4 - visible[draw]);
        if (rem <= 0) continue;

        counts13[draw]++;
        const nextSh = calcStandardShantenFromCounts([...counts13]);
        if (nextSh < shAfter) {
          let bestNextDisc = -1, bestNextCnt = 0, bestNextTypes = 0, bestRank = -1, bestTags = [];
          for (let nd = 0; nd < 34; nd++) {
            if (!counts13[nd]) continue;
            counts13[nd]--;
            if (calcStandardShantenFromCounts([...counts13]) === nextSh) {
              let ukCnt = 0, ukTypes = 0;
              for (let t2 = 0; t2 < 34; t2++) {
                if (counts13[t2] >= 4) continue;
                // visible[t2] には元の手牌とドラ表示牌が含まれるため、draw 自身を引いた分だけ 1 減算
                const r2 = Math.max(0, 4 - visible[t2] - (t2 === draw ? 1 : 0));
                if (r2 <= 0) continue;
                counts13[t2]++;
                if (calcStandardShantenFromCounts([...counts13]) < nextSh) { ukCnt += r2; ukTypes++; }
                counts13[t2]--;
              }
              const ns = evaluate2And3ShantenStructure(counts13, doraIdx);
              const rk = ukCnt * 32 + ns.shapeScore * 14;
              if (rk > bestRank) {
                bestRank = rk; bestNextDisc = nd; bestNextCnt = ukCnt; bestNextTypes = ukTypes; bestTags = ns.tags;
              }
            }
            counts13[nd]++;
          }
          if (bestNextDisc !== -1) {
            ukeireList.push({ tile: draw, rem, subLabel: `次${bestNextCnt}枚` });
            totalUkeire += rem;
            weightedNextUkeire += rem * bestNextCnt;
            weightedNextRank += rem * bestRank;
            bestTags.forEach(tg => { tagWeightMap[tg] = (tagWeightMap[tg] || 0) + rem; });
            transitions.push({
              drawTile: draw,
              rem,
              nextDiscard: bestNextDisc,
              detailHtml: `${nextSh}シャンテン受入 ${bestNextTypes}種${bestNextCnt}枚`,
              badgeText: bestTags.slice(0, 3).join('・') || '好形進行',
              sortKey: bestNextCnt * 100 + bestRank
            });
          }
        }
        counts13[draw]--;
      }

      if (!ukeireList.length) continue;
      transitions.sort((a, b) => b.sortKey - a.sortKey);
      const nextStageAvgWidth = +(weightedNextUkeire / totalUkeire).toFixed(1);
      const topTags = Object.keys(tagWeightMap).sort((a, b) => tagWeightMap[b] - tagWeightMap[a]).slice(0, 3);
      const scoreMetric = Math.round(
        totalUkeire * 185 + nextStageAvgWidth * 260 + struct.shapeScore * 42 + (weightedNextRank / totalUkeire) * 8
      );

      candidates.push({
        discardTile,
        ukeireCount: totalUkeire,
        ukeireTypes: ukeireList.length,
        ukeireList,
        maxPoints: 0,
        avgPoints: 0,
        nextStageAvgWidth,
        yakuSummary: topTags.length ? topTags : ['好形変化'],
        transitions,
        scoreMetric
      });
    }
  }

  candidates.sort((a, b) => {
    if (b.scoreMetric !== a.scoreMetric) return b.scoreMetric - a.scoreMetric;
    if (b.ukeireCount !== a.ukeireCount) return b.ukeireCount - a.ukeireCount;
    return b.nextStageAvgWidth - a.nextStageAvgWidth;
  });

  return { currentShanten, problemCategory: category, doraIdx, candidates };
}

/* 5. 数値の大小関係に完全準拠した1対1直接比較による解説生成エンジン */
function buildReasoningText(prob, userTile) {
  const { analysis, problemLabel } = prob;
  const sh = analysis.currentShanten;
  const best = analysis.candidates[0];
  const second = analysis.candidates[1];
  const bestName = TILE_NAMES_JA[best.discardTile];

  const userCand = analysis.candidates.find(c => c.discardTile === userTile);
  const comp = (userTile !== best.discardTile && userCand) ? userCand : second;
  const compName = comp ? TILE_NAMES_JA[comp.discardTile] : '';
  const compPrefix = (userTile !== best.discardTile && userCand) ? `あなたが選んだ打${compName}` : `次点の打${compName}`;

  if (userTile !== best.discardTile && !userCand) {
    return `【${problemLabel}】打${TILE_NAMES_JA[userTile]}は完成面子や雀頭を壊してシャンテン数が戻ってしまいます。打${bestName}とすれば${sh === 0 ? 'テンパイ' : `${sh}シャンテン`}を維持し、${best.ukeireTypes}種${best.ukeireCount}枚の受け入れ（${best.yakuSummary.join('・')}）を確保できます。`;
  }

  if (sh === 0) {
    const waitsStr = best.ukeireList.map(u => `${TILE_NAMES_JA[u.tile]}(${u.rem}枚)`).join('・');
    let msg = `【${problemLabel}】打${bestName}で ${waitsStr} の【${best.ukeireTypes}種${best.ukeireCount}枚待ち】になります。`;
    if (comp) {
      const diff = best.ukeireCount - comp.ukeireCount;
      const compWaitsStr = comp.ukeireList.map(u => `${TILE_NAMES_JA[u.tile]}(${u.rem}枚)`).join('・');
      if (diff > 0) {
        msg += `${compPrefix}は ${compWaitsStr} の${comp.ukeireTypes}種${comp.ukeireCount}枚待ちとなるため、打${bestName}の方が待ちが${diff}枚広く最善です。`;
      } else if (diff === 0) {
        msg += `${compPrefix}も${comp.ukeireCount}枚待ちですが、打${bestName}の方が高目手役【${best.yakuSummary.join('・')}】の打点効率で勝ります。`;
      } else {
        msg += `${compPrefix}（${comp.ukeireCount}枚待ち）より待ち枚数は${Math.abs(diff)}枚少ないものの、打${bestName}は手役・打点効率で優位に立ちます。`;
      }
    }
    return msg;
  }

  const nextLabel = sh === 1 ? 'テンパイ時の平均待ち' : `${sh - 1}シャンテン時の平均受け入れ`;
  const bestYakuStr = best.yakuSummary.join('・');
  let msg = `【${problemLabel}】打${bestName}は有効牌${best.ukeireTypes}種${best.ukeireCount}枚（${nextLabel}${best.nextStageAvgWidth}枚・${bestYakuStr}）。`;

  if (!comp) return msg;

  const ukeireDiff = best.ukeireCount - comp.ukeireCount;
  const widthDiff = +(best.nextStageAvgWidth - comp.nextStageAvgWidth).toFixed(1);
  const uniqueYaku = best.yakuSummary.filter(y => !comp.yakuSummary.includes(y));

  if (ukeireDiff > 0) {
    msg += `${compPrefix}（${comp.ukeireTypes}種${comp.ukeireCount}枚）より受け入れが${ukeireDiff}枚広く`;
    if (uniqueYaku.length > 0) {
      msg += `、さらに【${uniqueYaku.join('・')}】も狙えるため受け入れ・手役の両面で優位です。`;
    } else if (widthDiff > 0) {
      msg += `、${nextLabel}も${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ広がるため好形変化にも優れています。`;
    } else {
      msg += `、複合形をロスなく活かせます。`;
    }
  } else if (ukeireDiff === 0) {
    msg += `${compPrefix}も目先の有効牌は同じ${comp.ukeireTypes}種${comp.ukeireCount}枚ですが、`;
    if (uniqueYaku.length > 0 && sh === 1 && best.avgPoints > comp.avgPoints) {
      msg += `打${bestName}は【${uniqueYaku.join('・')}】が絡むためテンパイ時の期待打点（平均${best.avgPoints.toLocaleString()}点 vs ${comp.avgPoints.toLocaleString()}点）で優位に立ちます。`;
    } else if (uniqueYaku.length > 0) {
      msg += `打${bestName}は【${uniqueYaku.join('・')}】の種を残せるうえ、${nextLabel}も${best.nextStageAvgWidth}枚（打${compName}は${comp.nextStageAvgWidth}枚）と優秀です。`;
    } else if (widthDiff > 0) {
      msg += `1手進んだ際の${nextLabel}が打${compName}の${comp.nextStageAvgWidth}枚→打${bestName}の${best.nextStageAvgWidth}枚へ広がるため打${bestName}が最善です。`;
    } else if (widthDiff < 0) {
      msg += `${nextLabel}は打${compName}の${comp.nextStageAvgWidth}枚に対し打${bestName}は${best.nextStageAvgWidth}枚となりますが、複合形の質・手役面で打${bestName}が優位です。`;
    } else {
      msg += `形・手役面で打${bestName}が優位です。`;
    }
  } else {
    msg += `目先の枚数は${compPrefix}（${comp.ukeireTypes}種${comp.ukeireCount}枚）が${Math.abs(ukeireDiff)}枚広いものの、`;
    if (uniqueYaku.length > 0) {
      msg += `打${bestName}とすることで【${uniqueYaku.join('・')}】が狙え、`;
      if (widthDiff > 0) {
        msg += `${nextLabel}も${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ向上し、手役・最終形ともに勝ります。`;
      } else if (widthDiff < 0) {
        msg += `${nextLabel}は打${compName}の${comp.nextStageAvgWidth}枚に対し打${bestName}は${best.nextStageAvgWidth}枚ですが、手役・打点効率で逆転します。`;
      } else {
        msg += `最終打点効率で逆転します。`;
      }
    } else if (widthDiff > 0) {
      msg += `打${bestName}の方が好形ブロックを残せるため、${nextLabel}が${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ向上します。`;
    } else {
      msg += `${nextLabel}は打${compName}の${comp.nextStageAvgWidth}枚に対し打${bestName}は${best.nextStageAvgWidth}枚ですが、残すブロックの良形度・打点効率で打${bestName}が勝ります。`;
    }
  }

  return msg;
}

/* 6. 10大戦術アーキタイプ＋シャンテン数厳密検証つき難問生成アルゴリズム */
const ARCHETYPE_QUEUE = [];
const RECENT_HAND_HASHES = [];

function getNextArchetype() {
  if (ARCHETYPE_QUEUE.length === 0) {
    const all = [
      '2shanten_6block_choice',
      '1shanten_slide_tanyao',
      '3shanten_block_build',
      '1shanten_headless_kuttsuki',
      '2shanten_yaku_plan',
      '1shanten_sanshoku_ittsu',
      'menchin_multitenpai',
      '1shanten_three_pairs',
      'normal_multitenpai',
      'menchin_honitsu_1shanten'
    ];
    for (let i = all.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [all[i], all[j]] = [all[j], all[i]];
    }
    ARCHETYPE_QUEUE.push(...all);
  }
  return ARCHETYPE_QUEUE.pop();
}

function hasIsolatedTile(hand14, doraIdx) {
  const c = new Array(34).fill(0);
  hand14.forEach(t => c[t]++);
  for (let i = 0; i < 34; i++) {
    if (!c[i]) continue;
    if (i >= 27) { if (c[i] < 2) return true; continue; }
    if (c[i] >= 2 || i === doraIdx) continue;
    const pos = i % 9;
    const near = (pos >= 1 && c[i - 1] > 0) || (pos >= 2 && c[i - 2] > 0) || (pos <= 7 && c[i + 1] > 0) || (pos <= 6 && c[i + 2] > 0);
    if (!near) return true;
  }
  return false;
}

function tryBuildHardProblem(category) {
  const counts = new Array(34).fill(0);
  const mirror = Math.random() < 0.5;
  const mp = (p) => mirror ? (8 - p) : p;

  const add = (arr) => {
    for (const t of arr) if (t < 0 || t >= 34 || counts[t] >= 4) return false;
    for (const t of arr) counts[t]++;
    return true;
  };
  const addSuit = (suitBase, posArray) => add(posArray.map(p => suitBase + mp(p)));

  const suits = [0, 9, 18].sort(() => Math.random() - 0.5);
  const s1 = suits[0], s2 = suits[1], s3 = suits[2];
  const roundWindIdx = 27, seatWindIdx = pickRandom([27, 28, 29, 30]);
  let targetDoraTile = s1 + mp(pickRandom([2, 3, 4, 5]));
  let expectedShanten = 1;
  let label = '';

  if (category === 'menchin_multitenpai') {
    expectedShanten = 0;
    label = 'メンチン(清一色) 多面張テンパイ選択';
    const patterns14 = [
      [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8],
      [1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8],
      [0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 7, 8],
      [1, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8],
      [1, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 8]
    ];
    if (!addSuit(s1, pickRandom(patterns14))) return null;
    targetDoraTile = s1 + mp(pickRandom([2, 3, 4, 5]));
  } else if (category === 'menchin_honitsu_1shanten') {
    expectedShanten = 1;
    const isMenchin = Math.random() < 0.55;
    label = isMenchin ? 'メンチン(清一色) 1シャンテン最大受け入れ' : 'ホンイツ(混一色) 1シャンテン最大受け入れ';
    if (!isMenchin) {
      const h = pickRandom([27, seatWindIdx, 31, 32, 33]);
      if (!add([h, h, h])) return null;
      const p11 = [
        [1, 2, 2, 4, 4, 5, 6, 6, 7, 8, 8],
        [0, 1, 2, 4, 4, 5, 5, 7, 7, 8, 8],
        [1, 1, 2, 3, 5, 5, 6, 6, 7, 8, 8]
      ];
      if (!addSuit(s1, pickRandom(p11))) return null;
    } else {
      const p14 = [
        [1, 2, 2, 4, 4, 4, 6, 6, 7, 7, 7, 8, 8, 8],
        [1, 1, 2, 2, 4, 5, 5, 6, 6, 7, 8, 8, 8, 8]
      ];
      if (!addSuit(s1, pickRandom(p14))) return null;
    }
    targetDoraTile = s1 + mp(pickRandom([3, 4, 5]));
  } else if (category === 'normal_multitenpai') {
    expectedShanten = 0;
    label = '複合形 多面張テンパイ選択';
    const sub = pickRandom([0, 1, 2]);
    const st = pickRandom([1, 2, 3, 4]);
    if (sub === 0) {
      if (!addSuit(s1, [1, 2, 2, 3, 3, 4, 4, 5])) return null;
      if (!addSuit(s2, [st, st + 1, st + 2])) return null;
      if (!addSuit(s3, [2, 3, 3])) return null;
    } else if (sub === 1) {
      if (!addSuit(s1, [2, 3, 3, 4, 4, 5, 6])) return null;
      if (!addSuit(s2, [2, 3, 4, 5])) return null;
      if (!addSuit(s3, [st, st + 1, st + 2])) return null;
    } else {
      if (!addSuit(s1, [2, 3, 4, 4, 4, 5, 6, 6])) return null;
      if (!addSuit(s2, [st, st + 1, st + 2])) return null;
      if (!addSuit(s3, [3, 4, 5])) return null;
    }
    targetDoraTile = s1 + mp(3);
  } else if (category === '1shanten_slide_tanyao') {
    expectedShanten = 1;
    label = '1シャンテン 順子組み替え・手役移行';
    const sub = pickRandom([0, 1, 2]);
    if (sub === 0) {
      if (!addSuit(s1, [0, 1, 2, 3, 4, 4, 5, 6, 7])) return null;
      const p2 = pickRandom([2, 3, 4, 5]);
      if (!addSuit(s2, [p2, p2 + 1])) return null;
      const p3 = pickRandom([1, 2, 3, 4]);
      if (!addSuit(s3, [p3, p3 + 1, p3 + 1])) return null;
      targetDoraTile = s3 + mp(p3);
    } else if (sub === 1) {
      if (!addSuit(s1, [1, 2, 3, 4, 5, 5, 6, 7, 8])) return null;
      const p2 = pickRandom([2, 3, 4]);
      if (!addSuit(s2, [p2, p2 + 1])) return null;
      const p3 = pickRandom([2, 3, 4]);
      if (!addSuit(s3, [p3, p3, p3 + 1])) return null;
      targetDoraTile = s2 + mp(p2);
    } else {
      if (!addSuit(s1, [0, 1, 2, 3, 4, 5, 6])) return null;
      if (!addSuit(s2, [2, 3, 4, 5])) return null;
      if (!addSuit(s3, [2, 3, 3])) return null;
      targetDoraTile = s2 + mp(3);
    }
  } else if (category === '1shanten_sanshoku_ittsu') {
    expectedShanten = 1;
    label = '1シャンテン 三色・一通と好形受け入れの選択';
    const pos = pickRandom([1, 2, 3]);
    if (!addSuit(s1, [pos, pos + 1, pos + 2, pos + 3, pos + 3])) return null;
    if (!addSuit(s2, [pos, pos + 1, pos + 2, pos + 4, pos + 5])) return null;
    if (!addSuit(s3, [pos, pos + 1, pos + 3, pos + 4])) return null;
    targetDoraTile = s3 + mp(pos + 1);
  } else if (category === '1shanten_headless_kuttsuki') {
    expectedShanten = 1;
    label = '1シャンテン ヘッドレス・複合くっつき選択';
    const sub = pickRandom([0, 1]);
    if (sub === 0) {
      if (!addSuit(s1, [1, 2, 3, 4, 5])) return null;
      if (!addSuit(s2, [2, 3, 4, 5, 6])) return null;
      if (!addSuit(s3, [2, 3, 4, 6])) return null;
      targetDoraTile = s1 + mp(3);
    } else {
      if (!addSuit(s1, [1, 2, 3, 5, 6])) return null;
      if (!addSuit(s2, [2, 3, 4, 6, 7])) return null;
      if (!addSuit(s3, [2, 3, 4])) return null;
      targetDoraTile = s2 + mp(4);
    }
  } else if (category === '1shanten_three_pairs') {
    expectedShanten = 1;
    label = '1シャンテン 3対子・一盃口・複合ターツ選択';
    if (!addSuit(s1, [1, 1, 2, 2, 3])) return null;
    if (!addSuit(s2, [2, 3, 4, 5, 5])) return null;
    if (!addSuit(s3, [2, 3, 4])) return null;
    targetDoraTile = s1 + mp(2);
  } else if (category === '2shanten_6block_choice') {
    expectedShanten = 2;
    label = '2シャンテン→1シャンテン 6ブロック比較・二度受け整理';
    const sub = pickRandom([0, 1, 2]);
    if (sub === 0) {
      if (!addSuit(s1, [1, 2, 3, 5, 6])) return null;
      if (!addSuit(s2, [2, 3, 4, 6, 7])) return null;
      if (!addSuit(s3, [2, 3, 5, 6])) return null;
      targetDoraTile = s2 + mp(3);
    } else if (sub === 1) {
      if (!addSuit(s1, [1, 2, 3, 5, 5])) return null;
      if (!addSuit(s2, [2, 2, 3, 5, 5])) return null;
      if (!addSuit(s3, [3, 4, 4, 6])) return null;
      targetDoraTile = s3 + mp(3);
    } else {
      if (!addSuit(s1, [2, 3, 4, 6, 7])) return null;
      if (!addSuit(s2, [1, 2, 4, 5])) return null;
      if (!addSuit(s3, [2, 3, 5, 6, 6])) return null;
      targetDoraTile = s1 + mp(3);
    }
  } else if (category === '2shanten_yaku_plan') {
    expectedShanten = 2;
    label = '2シャンテン→1シャンテン 手役・好形構想';
    const pos = pickRandom([1, 2, 3]);
    if (Math.random() < 0.55) {
      if (!addSuit(s1, [pos, pos + 1, pos + 2, pos + 4, pos + 5])) return null;
      if (!addSuit(s2, [pos, pos + 1, pos + 4, pos + 5])) return null;
      if (!addSuit(s3, [pos, pos + 2, pos + 4, pos + 5])) return null;
      targetDoraTile = s2 + mp(pos + 1);
    } else {
      if (!addSuit(s1, [0, 1, 2, 3, 4, 6, 8])) return null;
      if (!addSuit(s2, [2, 3, 5, 6])) return null;
      if (!addSuit(s3, [3, 4, 4])) return null;
      targetDoraTile = s1 + mp(6);
    }
  } else {
    expectedShanten = 3;
    label = '3シャンテン→2シャンテン 序盤ブロック・手役構想';
    const pos = pickRandom([1, 2, 3]);
    if (!addSuit(s1, [pos, pos + 1, pos + 4, pos + 5])) return null;
    if (!addSuit(s2, [pos, pos + 2, pos + 4, pos + 5])) return null;
    if (!addSuit(s3, [pos, pos + 1, pos + 4, pos + 5, pos + 7])) return null;
    targetDoraTile = s3 + mp(pos + 1);
  }

  const hand14 = [];
  for (let i = 0; i < 34; i++) for (let k = 0; k < counts[i]; k++) hand14.push(i);
  if (hand14.length !== 14) return null;

  const doraInd = getIndicatorForDora(targetDoraTile);
  if (counts[doraInd] >= 4) return null;

  const doraIdx = getActualDoraIdx(doraInd);
  if (hasIsolatedTile(hand14, doraIdx)) return null;

  const handHash = hand14.join(',');
  if (RECENT_HAND_HASHES.includes(handHash)) return null;

  const analysis = analyze14Hand(hand14, roundWindIdx, seatWindIdx, doraInd, category);
  const sh = analysis.currentShanten;

  if (sh !== expectedShanten || analysis.candidates.length < 3) return null;

  const best = analysis.candidates[0];
  const second = analysis.candidates[1];
  const third = analysis.candidates[2];

  if (best.scoreMetric <= second.scoreMetric) return null;
  if (sh === 0 || category.startsWith('menchin')) {
    if (best.ukeireCount <= second.ukeireCount) return null;
    if (best.ukeireCount - second.ukeireCount > 6) return null;
  } else {
    if (Math.abs(best.ukeireCount - second.ukeireCount) >= 8) return null;
    if (best.ukeireCount < second.ukeireCount - 4) return null;
    if (best.ukeireCount - third.ukeireCount >= 12) return null;
  }

  RECENT_HAND_HASHES.push(handHash);
  if (RECENT_HAND_HASHES.length > 30) RECENT_HAND_HASHES.shift();

  return {
    roundWindIdx,
    seatWindIdx,
    doraIndicatorIdx: doraInd,
    hand14,
    problemLabel: label,
    analysis
  };
}

function generateInfiniteProblem() {
  for (let i = 0; i < 400; i++) {
    const arch = getNextArchetype();
    const p = tryBuildHardProblem(arch);
    if (p) return p;
  }
  const fb = [3, 4, 9, 10, 11, 12, 13, 13, 14, 15, 16, 19, 20, 20];
  return {
    roundWindIdx: 27,
    seatWindIdx: 28,
    doraIndicatorIdx: 12,
    hand14: fb,
    problemLabel: '1シャンテン 順子組み替え・手役移行',
    analysis: analyze14Hand(fb, 27, 28, 12, 'auto')
  };
}

/* 7. UIコントローラ＆イベントバインディング */
const STORAGE_KEY_REVIEW = 'mahjong_nanikiru_review_v8';
const STORAGE_KEY_STATS  = 'mahjong_nanikiru_stats_v8';

const state = {
  currentProb: null, answered: false, isReviewMode: false,
  reviewQueue: [], totalCount: 0, correctCount: 0, streak: 0, customTiles: []
};

const createProbId = (p) => `${p.roundWindIdx}_${p.seatWindIdx}_${p.doraIndicatorIdx}_${[...p.hand14].sort((a,b)=>a-b).join('.')}`;
const savePersistent = (k, d) => { try { localStorage.setItem(k, JSON.stringify(d)); } catch (e) {} };
const loadPersistent = (k, fb) => { try { const r = localStorage.getItem(k); return r ? JSON.parse(r) : fb; } catch (e) { return fb; } };

function updateHeaderAndStatsUI() {
  const rate = state.totalCount > 0 ? Math.round((state.correctCount / state.totalCount) * 100) : 0;
  document.getElementById('stat-total').textContent = `${state.totalCount}問`;
  document.getElementById('stat-accuracy').textContent = `${state.correctCount}問 (${rate}%)`;
  document.getElementById('stat-streak').textContent = `${state.streak}問`;

  const revBtn = document.getElementById('btn-toggle-review');
  const pill = document.getElementById('mode-indicator-pill');
  const cnt = state.reviewQueue.length;
  if (state.isReviewMode && cnt === 0) state.isReviewMode = false;

  if (state.isReviewMode) {
    revBtn.textContent = `通常出題へ (残${cnt}問)`;
    revBtn.className = 'px-2.5 py-1 rounded-lg bg-rose-600 text-white font-black text-[11px] sm:text-xs border border-rose-700 whitespace-nowrap transition';
    pill.classList.remove('hidden');
  } else {
    revBtn.textContent = `復習 (${cnt}問)`;
    revBtn.className = 'px-2.5 py-1 rounded-lg bg-rose-50 hover:bg-rose-100 text-rose-700 font-black text-[11px] sm:text-xs border border-rose-200 whitespace-nowrap transition';
    pill.classList.add('hidden');
  }
}

function renderActiveHandRack(tiles, onSelectTile) {
  const sortedHand = [...tiles].sort((a, b) => a - b);
  const handContainer = document.getElementById('hand-tiles-container');
  handContainer.innerHTML = sortedHand.map(tIdx => `<div class="tile-fluid-item" data-tile="${tIdx}">${renderTileSVG(tIdx)}</div>`).join('');
  handContainer.querySelectorAll('.tile-fluid-item').forEach(el => {
    el.addEventListener('click', () => onSelectTile(parseInt(el.dataset.tile, 10)));
  });
}

function loadProblemToUI(prob) {
  state.currentProb = prob;
  state.answered = false;

  const isDealer = prob.seatWindIdx === 27;
  const windBadge = document.getElementById('hud-wind-badge');
  windBadge.textContent = `${TILE_NAMES_JA[prob.roundWindIdx]}場 ${TILE_NAMES_JA[prob.seatWindIdx]}家(${isDealer ? '親' : '子'})`;
  windBadge.className = isDealer
    ? 'px-2 py-0.5 rounded-md bg-amber-600 text-white font-black text-xs shrink-0'
    : 'px-2 py-0.5 rounded-md bg-emerald-600 text-white font-black text-xs shrink-0';

  document.getElementById('hud-dora-tile').innerHTML = renderTileSVG(prob.doraIndicatorIdx);

  renderActiveHandRack(prob.hand14, (t) => handleSelectDiscard(t));

  const uniqueTiles = Array.from(new Set([...prob.hand14].sort((a, b) => a - b)));
  const choicesGrid = document.getElementById('discard-choices-grid');
  choicesGrid.innerHTML = uniqueTiles.map(tIdx => `
    <button type="button" data-tile="${tIdx}" class="tenkey-btn flex flex-col items-center justify-center p-1.5 rounded-xl bg-slate-50 hover:bg-emerald-50 border border-slate-300 hover:border-emerald-400">
      <div class="w-8 sm:w-9">${renderTileSVG(tIdx)}</div>
      <span class="text-[11px] font-black text-slate-700 mt-1">${TILE_NAMES_JA[tIdx]}</span>
    </button>
  `).join('');
  choicesGrid.querySelectorAll('button').forEach(btn => {
    btn.addEventListener('click', () => handleSelectDiscard(parseInt(btn.dataset.tile, 10)));
  });

  document.getElementById('answer-section').classList.remove('hidden');
  document.getElementById('result-section').classList.add('hidden');
}

function startNextProblem() {
  document.getElementById('custom-panel').classList.add('hidden');
  if (state.isReviewMode && state.reviewQueue.length > 0) {
    const raw = pickRandom(state.reviewQueue);
    const analysis = analyze14Hand(raw.hand14, raw.roundWindIdx, raw.seatWindIdx, raw.doraIndicatorIdx, raw.category || 'auto');
    loadProblemToUI({ ...raw, analysis });
    return;
  }
  loadProblemToUI(generateInfiniteProblem());
}

function handleSelectDiscard(userTile) {
  if (state.answered) return;
  state.answered = true;
  const prob = state.currentProb;
  const best = prob.analysis.candidates[0];
  const isCorrect = userTile === best.discardTile;

  state.totalCount++;
  if (isCorrect) { state.correctCount++; state.streak++; } else { state.streak = 0; }
  savePersistent(STORAGE_KEY_STATS, { totalCount: state.totalCount, correctCount: state.correctCount, streak: state.streak });

  const probId = createProbId(prob);
  const statusMsg = document.getElementById('review-status-msg');
  if (!isCorrect) {
    if (!state.reviewQueue.some(item => createProbId(item) === probId)) {
      state.reviewQueue.push({
        roundWindIdx: prob.roundWindIdx, seatWindIdx: prob.seatWindIdx,
        doraIndicatorIdx: prob.doraIndicatorIdx, hand14: [...prob.hand14],
        problemLabel: prob.problemLabel, category: prob.analysis.problemCategory
      });
      savePersistent(STORAGE_KEY_REVIEW, state.reviewQueue);
    }
    statusMsg.textContent = '📌 間違えた問題を復習リストに保存しました';
  } else if (state.isReviewMode) {
    state.reviewQueue = state.reviewQueue.filter(item => createProbId(item) !== probId);
    savePersistent(STORAGE_KEY_REVIEW, state.reviewQueue);
    statusMsg.textContent = '✓ 復習リストからクリアしました';
  } else {
    statusMsg.textContent = '復習リストに保存できます';
  }

  updateHeaderAndStatsUI();
  renderResultSection(prob, userTile, isCorrect);
}

function renderResultSection(prob, userTile, isCorrect) {
  document.getElementById('answer-section').classList.add('hidden');
  document.getElementById('result-section').classList.remove('hidden');

  const sh = prob.analysis.currentShanten;
  const best = prob.analysis.candidates[0];
  const vBanner = document.getElementById('verdict-banner');
  const vBadge = document.getElementById('verdict-badge');
  const vTitle = document.getElementById('verdict-title');
  const vWaitCount = document.getElementById('verdict-WaitCount');
  const vBestTile = document.getElementById('verdict-best-tile');
  const vUserRow = document.getElementById('verdict-user-row');
  const vUserAns = document.getElementById('verdict-user-ans');

  vWaitCount.textContent = sh === 0
    ? `待ち ${best.ukeireTypes}種${best.ukeireCount}枚`
    : `有効牌 ${best.ukeireTypes}種${best.ukeireCount}枚 (次平均${best.nextStageAvgWidth}枚)`;
  vBestTile.innerHTML = `<span class="mini-tile">${renderTileSVG(best.discardTile, { highlight: true })}</span><span>打 ${TILE_NAMES_JA[best.discardTile]}</span>`;

  if (isCorrect) {
    vBanner.className = 'rounded-2xl p-3.5 border-2 border-emerald-500 bg-emerald-50/70 shadow-sm space-y-2';
    vBadge.className = 'px-2.5 py-0.5 rounded-md bg-emerald-600 text-white text-xs font-black shrink-0';
    vBadge.textContent = '正解';
    vTitle.textContent = '最善手です！';
    vUserRow.classList.add('hidden');
  } else {
    vBanner.className = 'rounded-2xl p-3.5 border-2 border-rose-500 bg-rose-50/70 shadow-sm space-y-2';
    vBadge.className = 'px-2.5 py-0.5 rounded-md bg-rose-600 text-white text-xs font-black shrink-0';
    vBadge.textContent = '不正解';
    vTitle.textContent = `最善は「打${TILE_NAMES_JA[best.discardTile]}」`;
    vUserRow.classList.remove('hidden');
    vUserAns.innerHTML = `<span class="inline-flex items-center gap-1"><span class="mini-tile-sm">${renderTileSVG(userTile)}</span><span>打 ${TILE_NAMES_JA[userTile]}</span></span>`;
  }

  document.getElementById('explain-reasoning').textContent = buildReasoningText(prob, userTile);
  document.getElementById('ukeire-section-title').textContent = sh === 0
    ? `打${TILE_NAMES_JA[best.discardTile]} の待ち牌一覧`
    : `打${TILE_NAMES_JA[best.discardTile]} の有効牌（${sh}→${sh - 1}シャンテン進行）`;
  document.getElementById('ukeire-total-badge').textContent = `合計 ${best.ukeireTypes}種 ${best.ukeireCount}枚`;

  document.getElementById('best-ukeire-tiles').innerHTML = best.ukeireList.map(u => `
    <div class="flex items-center gap-1 bg-slate-50 border border-slate-200 rounded-lg px-2 py-1">
      <span class="mini-tile">${renderTileSVG(u.tile)}</span>
      <div class="text-[11px] leading-tight">
        <div class="font-black text-slate-800">${TILE_NAMES_JA[u.tile]} <span class="text-emerald-700">残${u.rem}</span></div>
        <div class="text-[10px] font-bold text-slate-500">${u.subLabel}</div>
      </div>
    </div>
  `).join('');

  const transEl = document.getElementById('best-tenpai-transitions');
  transEl.innerHTML = (best.transitions || []).slice(0, 8).map(tr => `
    <div class="py-1.5 flex items-center justify-between gap-2 whitespace-nowrap overflow-x-auto">
      <div class="flex items-center gap-1.5">
        <span class="text-slate-500 font-bold">ツモ</span>
        <span class="mini-tile">${renderTileSVG(tr.drawTile)}</span>
        <span class="text-slate-400">→</span>
        <span class="font-bold text-slate-700">打</span>
        <span class="mini-tile-sm">${renderTileSVG(tr.nextDiscard)}</span>
        <span class="font-black text-emerald-700">(${tr.detailHtml})</span>
      </div>
      <span class="px-1.5 py-0.5 rounded bg-indigo-50 text-indigo-700 font-bold text-[10px] shrink-0">${tr.badgeText}</span>
    </div>
  `).join('');

  const modeLabel = sh === 0 ? '待ち' : '有効牌';
  document.getElementById('candidate-comparison-list').innerHTML = prob.analysis.candidates.map((cand, idx) => {
    const isUser = cand.discardTile === userTile;
    const badge = idx === 0
      ? `<span class="px-1.5 py-0.5 rounded bg-emerald-600 text-white font-black text-[10px]">最善</span>`
      : `<span class="px-1.5 py-0.5 rounded bg-slate-200 text-slate-700 font-bold text-[10px]">${idx + 1}位</span>`;
    const userBadge = isUser ? `<span class="px-1.5 py-0.5 rounded bg-amber-100 text-amber-900 border border-amber-300 font-black text-[10px]">選択</span>` : '';
    const yakuText = cand.yakuSummary.join('・') || 'リーチ';
    const rightMetric = sh === 0
      ? `平均${cand.avgPoints.toLocaleString()}点`
      : sh === 1
        ? `平均待${cand.nextStageAvgWidth}枚 / ${cand.avgPoints.toLocaleString()}点`
        : `1手先平均 ${cand.nextStageAvgWidth}枚`;

    const miniUkeireTilesHtml = cand.ukeireList.map(u =>
      `<span class="mini-tile-sm" title="${TILE_NAMES_JA[u.tile]} (残${u.rem}枚)">${renderTileSVG(u.tile)}</span>`
    ).join('');

    return `
      <div class="py-2 space-y-1.5 ${idx === 0 ? 'bg-emerald-50/40 -mx-2 px-2 rounded-lg' : ''}">
        <div class="flex items-center justify-between gap-2 whitespace-nowrap">
          <div class="flex items-center gap-1.5">${badge}${userBadge}<span class="mini-tile">${renderTileSVG(cand.discardTile)}</span><span class="font-black text-slate-900">打 ${TILE_NAMES_JA[cand.discardTile]}</span></div>
          <div class="flex items-center gap-2 font-mono"><span class="font-black text-emerald-700">${cand.ukeireTypes}種${cand.ukeireCount}枚</span><span class="text-slate-300">|</span><span class="font-black text-indigo-700">${rightMetric}</span></div>
        </div>
        <div class="flex items-center justify-between gap-2 text-[11px] text-slate-600">
          <div class="flex items-center flex-wrap gap-0.5 min-w-0">
            <span class="font-bold text-slate-500 mr-1 shrink-0">${modeLabel}:</span>
            ${miniUkeireTilesHtml}
          </div>
          <span class="shrink-0 font-bold text-indigo-800 self-start mt-0.5">[${yakuText}]</span>
        </div>
      </div>
    `;
  }).join('');
}

function initCustomInputMode() {
  const doraSelect = document.getElementById('custom-dora');
  doraSelect.innerHTML = TILE_NAMES_JA.map((n, i) => `<option value="${i}">${n}</option>`).join('');
  doraSelect.value = '3';

  const palette = document.getElementById('custom-palette');
  palette.innerHTML = TILE_NAMES_JA.map((n, i) => `<button type="button" data-tile="${i}" class="p-0.5 rounded hover:bg-indigo-100 active:scale-95 transition" title="${n}">${renderTileSVG(i)}</button>`).join('');

  const errEl = document.getElementById('custom-error-msg');
  const showCustomErr = (msg) => {
    errEl.textContent = msg;
    errEl.classList.remove('hidden');
  };
  const clearCustomErr = () => errEl.classList.add('hidden');

  const updateCustomPreview = () => {
    document.getElementById('custom-count').textContent = state.customTiles.length;
    clearCustomErr();
    if (state.customTiles.length > 0) {
      const sorted = [...state.customTiles].sort((a, b) => a - b);
      document.getElementById('hand-tiles-container').innerHTML = sorted.map((t, idx) =>
        `<div class="tile-fluid-item" data-rm="${idx}" title="タップで1枚削除">${renderTileSVG(t)}</div>`
      ).join('');
      document.querySelectorAll('#hand-tiles-container [data-rm]').forEach(el => {
        el.addEventListener('click', () => {
          const rIdx = parseInt(el.dataset.rm, 10);
          const sortedCopy = [...state.customTiles].sort((a, b) => a - b);
          sortedCopy.splice(rIdx, 1);
          state.customTiles = sortedCopy;
          updateCustomPreview();
        });
      });
    } else if (state.currentProb) {
      renderActiveHandRack(state.currentProb.hand14, (t) => handleSelectDiscard(t));
    }
  };

  palette.querySelectorAll('button').forEach(btn => {
    btn.addEventListener('click', () => {
      if (state.customTiles.length >= 14) { showCustomErr('手牌は14枚までです'); return; }
      const t = parseInt(btn.dataset.tile, 10);
      if (state.customTiles.filter(x => x === t).length >= 4) { showCustomErr(`${TILE_NAMES_JA[t]}は4枚までです`); return; }
      state.customTiles.push(t);
      updateCustomPreview();
    });
  });

  document.getElementById('btn-custom-clear').addEventListener('click', () => {
    state.customTiles = [];
    updateCustomPreview();
  });

  document.getElementById('btn-custom-close').addEventListener('click', () => {
    document.getElementById('custom-panel').classList.add('hidden');
    clearCustomErr();
    if (state.currentProb) {
      renderActiveHandRack(state.currentProb.hand14, (t) => handleSelectDiscard(t));
    }
  });

  document.getElementById('btn-custom-analyze').addEventListener('click', () => {
    if (state.customTiles.length !== 14) {
      showCustomErr(`あと${14 - state.customTiles.length}枚選択してください`);
      return;
    }
    const seat = parseInt(document.getElementById('custom-seat').value, 10);
    const dora = parseInt(document.getElementById('custom-dora').value, 10);
    const analysis = analyze14Hand(state.customTiles, 27, seat, dora, 'auto');
    if (!analysis.candidates.length) {
      showCustomErr('有効な打牌候補が見つかりませんでした（シャンテン数を確認してください）');
      return;
    }
    document.getElementById('custom-panel').classList.add('hidden');
    clearCustomErr();
    loadProblemToUI({
      roundWindIdx: 27,
      seatWindIdx: seat,
      doraIndicatorIdx: dora,
      hand14: [...state.customTiles],
      problemLabel: `手牌解析（${analysis.currentShanten === 0 ? 'テンパイ' : `${analysis.currentShanten}シャンテン`}）`,
      analysis
    });
  });
}

window.addEventListener('DOMContentLoaded', () => {
  state.reviewQueue = loadPersistent(STORAGE_KEY_REVIEW, []);
  const st = loadPersistent(STORAGE_KEY_STATS, { totalCount: 0, correctCount: 0, streak: 0 });
  state.totalCount = st.totalCount || 0; state.correctCount = st.correctCount || 0; state.streak = st.streak || 0;

  updateHeaderAndStatsUI();
  initCustomInputMode();

  document.getElementById('btn-generate-next').addEventListener('click', startNextProblem);
  document.getElementById('btn-next-after-result').addEventListener('click', startNextProblem);
  document.getElementById('btn-toggle-review').addEventListener('click', () => {
    if (!state.isReviewMode && !state.reviewQueue.length) return;
    state.isReviewMode = !state.isReviewMode;
    updateHeaderAndStatsUI();
    startNextProblem();
  });
  document.getElementById('btn-toggle-custom').addEventListener('click', () => {
    const panel = document.getElementById('custom-panel');
    panel.classList.toggle('hidden');
    if (!panel.classList.contains('hidden')) {
      document.getElementById('custom-count').textContent = state.customTiles.length;
    } else if (state.currentProb) {
      renderActiveHandRack(state.currentProb.hand14, (t) => handleSelectDiscard(t));
    }
  });
  document.getElementById('btn-reset-stats').addEventListener('click', () => {
    state.totalCount = 0; state.correctCount = 0; state.streak = 0;
    savePersistent(STORAGE_KEY_STATS, { totalCount: 0, correctCount: 0, streak: 0 });
    updateHeaderAndStatsUI();
  });
  document.getElementById('btn-toggle-bookmark').addEventListener('click', () => {
    const p = state.currentProb;
    if (!p) return;
    const id = createProbId(p);
    if (state.reviewQueue.some(item => createProbId(item) === id)) {
      state.reviewQueue = state.reviewQueue.filter(item => createProbId(item) !== id);
      document.getElementById('review-status-msg').textContent = '復習リストから削除しました';
    } else {
      state.reviewQueue.push({ roundWindIdx: p.roundWindIdx, seatWindIdx: p.seatWindIdx, doraIndicatorIdx: p.doraIndicatorIdx, hand14: [...p.hand14], problemLabel: p.problemLabel, category: p.analysis.problemCategory });
      document.getElementById('review-status-msg').textContent = '📌 復習リストに保存しました';
    }
    savePersistent(STORAGE_KEY_REVIEW, state.reviewQueue);
    updateHeaderAndStatsUI();
  });

  startNextProblem();
});