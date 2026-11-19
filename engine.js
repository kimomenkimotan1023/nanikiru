/*************************************************************************
 * 麻雀 実戦何切るトレーナー 実戦ツモ進行＆厳密解析エンジン (engine.js)
 * - 固定テンプレート全廃：10種の牌山プロファイルからの動的生成
 * - 近傍枝刈り高速化＋2手先読み期待値合算評価＋同格良手判定
 * - 0 / 1 / 2 / 3シャンテン厳密検証・全役/符/切り上げ満貫対応・1対1比較解説
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

/**
 * 4面子1雀頭においてシャンテン数を進め得る候補牌のみを返す（数学的等価な高速化）
 */
function getRelevantTiles(counts) {
  const rel = [];
  for (let t = 0; t < 34; t++) {
    if (counts[t] >= 4) continue;
    if (counts[t] > 0) {
      rel.push(t);
    } else if (t < 27) {
      const pos = t % 9;
      if (
        (pos >= 1 && counts[t - 1] > 0) ||
        (pos >= 2 && counts[t - 2] > 0) ||
        (pos <= 7 && counts[t + 1] > 0) ||
        (pos <= 6 && counts[t + 2] > 0)
      ) {
        rel.push(t);
      }
    }
  }
  return rel;
}

/**
 * 最善手と実戦上「同格の良手」かを厳密判定する
 */
function isEquivalentGoodDiscard(best, cand, shanten) {
  if (!best || !cand) return false;
  if (best.discardTile === cand.discardTile) return true;
  if (cand.ukeireCount !== best.ukeireCount) return false;

  const sameWidth = Math.abs(best.nextStageAvgWidth - cand.nextStageAvgWidth) <= 0.3;
  const sameYaku = best.yakuSummary.join(',') === cand.yakuSummary.join(',');
  const closeScore = cand.scoreMetric >= best.scoreMetric * 0.975;

  if (shanten <= 1) {
    const samePts = Math.abs(best.avgPoints - cand.avgPoints) <= 300;
    return sameWidth && samePts && (sameYaku || Math.abs(best.maxPoints - cand.maxPoints) <= 500) && closeScore;
  }
  return sameWidth && sameYaku && closeScore;
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

/* 2. 14枚アガリ役・符・打点計算（小三元・混老頭・三色同刻・役満・切り上げ満貫対応） */
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

        const koutsuTiles = [];
        let dragonKoutsu = 0;
        mentsu.forEach(m => {
          if (m.kind === 'koutsu') {
            const t = m.tiles[0];
            koutsuTiles.push(t);
            if (t === roundWind && t === seatWind) yaku.push({ name: `ダブ${TILE_NAMES_JA[t]}`, han: 2 });
            else if (t === roundWind || t === seatWind) yaku.push({ name: `役牌 ${TILE_NAMES_JA[t]}`, han: 1 });
            if (t >= 31) {
              dragonKoutsu++;
              yaku.push({ name: `役牌 ${TILE_NAMES_JA[t]}`, han: 1 });
            }
          }
        });

        // 小三元・大三元
        if (dragonKoutsu === 3) {
          yaku.push({ name: '大三元', han: 13 });
        } else if (dragonKoutsu === 2 && jIdx >= 31) {
          yaku.push({ name: '小三元', han: 2 });
        }

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
        for (let pos = 0; pos <= 8; pos++) {
          if (koutsuTiles.includes(pos) && koutsuTiles.includes(9 + pos) && koutsuTiles.includes(18 + pos)) {
            yaku.push({ name: '三色同刻', han: 2 }); break;
          }
        }
        for (const sb of [0, 9, 18]) {
          if (sKeys.includes(sb) && sKeys.includes(sb + 3) && sKeys.includes(sb + 6)) {
            yaku.push({ name: '一気通貫', han: 2 }); break;
          }
        }

        const koutsuCount = koutsuTiles.length;
        if (koutsuCount === 4) yaku.push({ name: '対々和', han: 2 });
        const ankouRonCount = mentsu.filter((m, idx) => m.kind === 'koutsu' && idx !== wc.mIdx).length;
        if (ankouRonCount >= 3) yaku.push({ name: '三暗刻', han: 2 });

        const hasShuntsu = mentsu.some(m => m.kind === 'shuntsu');
        const allYao = mentsu.every(m => m.tiles.some(t => isYaochu(t))) && isYaochu(jIdx);
        const hasHonor = allTiles.some(t => t >= 27);
        const allHonors = allTiles.every(t => t >= 27);

        if (allHonors) {
          yaku.push({ name: '字一色', han: 13 });
        } else if (allYao) {
          if (!hasShuntsu) {
            yaku.push({ name: hasHonor ? '混老頭' : '清老頭', han: hasHonor ? 2 : 13 });
          } else {
            yaku.push({ name: hasHonor ? '混全帯幺九' : '純全帯幺九', han: hasHonor ? 2 : 3 });
          }
        }

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
          if (isYakuhaiPair) rawFu += 2; // 連風牌雀頭も2符
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

  const relTiles = getRelevantTiles(counts13);
  for (const t of relTiles) {
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

/* 3. 2〜3シャンテン専用：ブロック・手役（偽一通排除・役牌対応）・好形評価器 */
function hasValidIttsuBlocks(counts13, suitOffset) {
  const c = counts13.slice(suitOffset, suitOffset + 9);
  const seg1 = (c[0] > 0 ? 1 : 0) + (c[1] > 0 ? 1 : 0) + (c[2] > 0 ? 1 : 0);
  const seg2 = (c[3] > 0 ? 1 : 0) + (c[4] > 0 ? 1 : 0) + (c[5] > 0 ? 1 : 0);
  const seg3 = (c[6] > 0 ? 1 : 0) + (c[7] > 0 ? 1 : 0) + (c[8] > 0 ? 1 : 0);
  // 2345678（1と9が両方欠落）を誤って一気通貫と判定しないよう端牌構成を厳密チェック
  const hasEdgeAnchor = (seg1 === 3) || (seg3 === 3) || (c[0] > 0 && c[8] > 0);
  return seg1 >= 2 && seg2 >= 2 && seg3 >= 2 && (seg1 + seg2 + seg3 >= 7) && hasEdgeAnchor;
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

function evaluate2And3ShantenStructure(counts13, doraIdx, roundWind, seatWind) {
  let score = 0;
  const tags = [];
  const doraCnt = counts13[doraIdx];

  const suitCounts = [0, 0, 0];
  let honorCnt = 0, yaoCnt = 0, koutsuSeedCnt = 0, hasYakuhai = false;
  for (let i = 0; i < 34; i++) {
    const c = counts13[i];
    if (!c) continue;
    if (c >= 3) koutsuSeedCnt++;
    if (isYaochu(i)) yaoCnt += c;
    if (i < 27) {
      suitCounts[Math.floor(i / 9)] += c;
    } else {
      honorCnt += c;
      const isYakuTile = i >= 31 || i === roundWind || i === seatWind;
      if (isYakuTile && c >= 3) { score += 50; hasYakuhai = true; }
      else if (isYakuTile && c === 2) { score += 24; hasYakuhai = true; }
    }
  }

  const maxSuit = Math.max(...suitCounts);
  if (maxSuit + honorCnt === 13) {
    score += honorCnt === 0 ? 140 : 95;
    tags.push(honorCnt === 0 ? '清一色' : '混一色');
  } else if (maxSuit + honorCnt >= 11) {
    score += 36;
    tags.push(honorCnt === 0 ? '清一色含み' : '混一色含み');
  }
  if (yaoCnt === 0) {
    score += 45;
    tags.push('断幺九');
  }
  if (hasYakuhai) tags.push('役牌');
  if (koutsuSeedCnt >= 2) {
    score += 35;
    tags.push('暗刻・対子系');
  }
  if (hasValidSanshokuBlocks(counts13)) {
    score += 65;
    tags.push('三色同順');
  }
  if (hasValidIttsuBlocks(counts13, 0) || hasValidIttsuBlocks(counts13, 9) || hasValidIttsuBlocks(counts13, 18)) {
    score += 60;
    tags.push('一気通貫');
  }

  let hasGoodComplex = false;
  for (let s = 0; s < 3; s++) {
    const b = s * 9;
    for (let p = 0; p <= 6; p++) {
      if (counts13[b + p] >= 2 && counts13[b + p + 1] >= 2 && counts13[b + p + 2] >= 2) {
        score += 35;
        if (!tags.includes('一盃口')) tags.push('一盃口');
      }
    }
    let suitComplex = 0;
    for (let p = 1; p <= 4; p++) {
      if (counts13[b + p] > 0 && counts13[b + p + 1] > 0 && counts13[b + p + 2] > 0 && counts13[b + p + 3] > 0) {
        suitComplex = Math.max(suitComplex, 14);
      }
    }
    for (let p = 1; p <= 5; p++) {
      if (counts13[b + p] > 0 && counts13[b + p + 1] >= 2 && counts13[b + p + 2] > 0) {
        suitComplex = Math.max(suitComplex, 14);
      }
    }
    if (suitComplex > 0) { score += suitComplex; hasGoodComplex = true; }
    if (counts13[b] > 0 && counts13[b + 1] > 0 && counts13[b + 2] === 0) score -= 20;
    if (counts13[b + 8] > 0 && counts13[b + 7] > 0 && counts13[b + 6] === 0) score -= 20;
  }

  if (doraCnt > 0) {
    score += doraCnt * 32;
    tags.push(`ドラ${doraCnt}`);
  }
  if (tags.length === 0) tags.push(hasGoodComplex ? '好形連続形' : '好形変化');

  return { shapeScore: score, tags };
}

/* 4. 14枚手牌の全打牌候補ソルバー（近傍枝刈り高速化済み） */
function analyze14Hand(hand14, roundWind, seatWind, doraInd, category = 'auto') {
  const doraIdx = getActualDoraIdx(doraInd);
  const fullCounts = new Array(34).fill(0);
  hand14.forEach(t => fullCounts[t]++);
  const visible = [...fullCounts];
  visible[doraInd]++;

  const suitTotals = [0, 0, 0];
  let honorTotal = 0;
  hand14.forEach(t => { if (t < 27) suitTotals[Math.floor(t / 9)]++; else honorTotal++; });
  const isFlushHand = (Math.max(...suitTotals) + honorTotal >= 13) || category === 'sim_0s_menchin';

  const currentShanten = calcStandardShantenFromCounts([...fullCounts]);
  if (currentShanten < 0) {
    return { currentShanten, problemCategory: category, doraIdx, candidates: [] };
  }

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
      const relDraws = getRelevantTiles(counts13);

      for (const draw of relDraws) {
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
      const struct = evaluate2And3ShantenStructure(counts13, doraIdx, roundWind, seatWind);
      const ukeireList = [], transitions = [];
      let totalUkeire = 0, weightedNextUkeire = 0, weightedNextEvSum = 0;
      const tagWeightMap = {};
      struct.tags.forEach(t => { tagWeightMap[t] = 10; });

      const relDraws = getRelevantTiles(counts13);
      for (const draw of relDraws) {
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
              const relT2 = getRelevantTiles(counts13);
              for (const t2 of relT2) {
                const r2 = Math.max(0, 4 - visible[t2] - (t2 === draw ? 1 : 0));
                if (r2 <= 0) continue;
                counts13[t2]++;
                if (calcStandardShantenFromCounts([...counts13]) < nextSh) { ukCnt += r2; ukTypes++; }
                counts13[t2]--;
              }
              const ns = evaluate2And3ShantenStructure(counts13, doraIdx, roundWind, seatWind);
              const rk = ukCnt * 40 + ns.shapeScore * 10;
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
            weightedNextEvSum += rem * (bestNextCnt * 18 + bestRank * 0.15);
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
      const scoreMetric = Math.round(totalUkeire * 220 + weightedNextEvSum + struct.shapeScore * 35);

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

/* 5. 数値の大小関係・同格良手・期待打点差に完全準拠した1対1比較解説エンジン */
function buildReasoningText(prob, userTile) {
  const { analysis, problemLabel } = prob;
  const sh = analysis.currentShanten;
  const best = analysis.candidates[0];
  const second = analysis.candidates[1];
  const bestName = TILE_NAMES_JA[best.discardTile];

  const userCand = analysis.candidates.find(c => c.discardTile === userTile);
  if (userTile !== best.discardTile && userCand && isEquivalentGoodDiscard(best, userCand, sh)) {
    return `【${problemLabel}】あなたが選んだ打${TILE_NAMES_JA[userTile]}と打${bestName}は、受け入れ（${userCand.ukeireTypes}種${userCand.ukeireCount}枚）・1手先の広さ・手役（${userCand.yakuSummary.join('・')}）がいずれも同格の良手です。場況や安全度（先切り）に応じて使い分けられる実戦上どちらも正解の選択です。`;
  }

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
        if (best.avgPoints > comp.avgPoints) {
          msg += `${compPrefix}も${comp.ukeireCount}枚待ちですが、打${bestName}は平均${best.avgPoints.toLocaleString()}点（打${compName}は${comp.avgPoints.toLocaleString()}点）と打点効率で勝ります。`;
        } else if (best.ukeireTypes > comp.ukeireTypes) {
          msg += `${compPrefix}も${comp.ukeireCount}枚待ちですが、打${bestName}の方が待ち種類が多く（${best.ukeireTypes}種 vs ${comp.ukeireTypes}種）出アガリしやすさで勝ります。`;
        } else {
          msg += `${compPrefix}も${comp.ukeireCount}枚待ちですが、手役構成（${best.yakuSummary.join('・')}）で打${bestName}が優位です。`;
        }
      } else {
        msg += `${compPrefix}（${comp.ukeireCount}枚待ち）より待ち枚数は${Math.abs(diff)}枚少ないものの、打${bestName}は平均${best.avgPoints.toLocaleString()}点（打${compName}は${comp.avgPoints.toLocaleString()}点）と打点効率で優位に立ちます。`;
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
  const ptsDiff = sh === 1 ? (best.avgPoints - comp.avgPoints) : 0;
  const uniqueYaku = best.yakuSummary.filter(y => !comp.yakuSummary.includes(y));

  if (ukeireDiff > 0) {
    msg += `${compPrefix}（${comp.ukeireTypes}種${comp.ukeireCount}枚）より受け入れが${ukeireDiff}枚広く`;
    if (uniqueYaku.length > 0) {
      msg += `、さらに【${uniqueYaku.join('・')}】も狙えるため受け入れ・手役の両面で優位です。`;
    } else if (widthDiff > 0) {
      msg += `、${nextLabel}も${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ広がるため好形変化にも優れています。`;
    } else if (ptsDiff > 300) {
      msg += `、テンパイ時の期待打点も平均${comp.avgPoints.toLocaleString()}点→${best.avgPoints.toLocaleString()}点と高くなります。`;
    } else {
      msg += `、複合形をロスなく活かせます。`;
    }
  } else if (ukeireDiff === 0) {
    msg += `${compPrefix}も目先の有効牌は同じ${comp.ukeireTypes}種${comp.ukeireCount}枚ですが、`;
    if (sh === 1 && ptsDiff > 300) {
      const yakuNote = uniqueYaku.length > 0 ? `【${uniqueYaku.join('・')}】が絡み` : '高打点ルートの比率が高く';
      msg += `打${bestName}は${yakuNote}テンパイ時の期待打点（平均${best.avgPoints.toLocaleString()}点 vs ${comp.avgPoints.toLocaleString()}点）で優位に立ちます。`;
    } else if (uniqueYaku.length > 0) {
      if (widthDiff > 0) {
        msg += `打${bestName}は【${uniqueYaku.join('・')}】の種を残せるうえ、${nextLabel}も${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ広がります。`;
      } else if (widthDiff < 0) {
        msg += `打${bestName}は【${uniqueYaku.join('・')}】の種を残せるため、${nextLabel}（${best.nextStageAvgWidth}枚 vs 打${compName}は${comp.nextStageAvgWidth}枚）の差を補って手役面で優位です。`;
      } else {
        msg += `打${bestName}は【${uniqueYaku.join('・')}】の種を残せるため手役・打点面で優位です。`;
      }
    } else if (widthDiff > 0) {
      msg += `1手進んだ際の${nextLabel}が打${compName}の${comp.nextStageAvgWidth}枚→打${bestName}の${best.nextStageAvgWidth}枚へ広がるため打${bestName}が最善です。`;
    } else if (widthDiff < 0) {
      msg += `${nextLabel}は打${compName}の${comp.nextStageAvgWidth}枚に対し打${bestName}は${best.nextStageAvgWidth}枚となりますが、残すブロックの好形度・手役面で打${bestName}が優位です。`;
    } else {
      msg += `形・手役面で打${bestName}が優位です。`;
    }
  } else {
    msg += `目先の枚数は${compPrefix}（${comp.ukeireTypes}種${comp.ukeireCount}枚）が${Math.abs(ukeireDiff)}枚広いものの、`;
    if (uniqueYaku.length > 0) {
      msg += `打${bestName}とすることで【${uniqueYaku.join('・')}】が狙え、`;
      if (widthDiff > 0) {
        msg += `${nextLabel}も${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ向上し、手役・最終形ともに勝ります。`;
      } else if (sh === 1 && ptsDiff > 300) {
        msg += `期待打点が平均${comp.avgPoints.toLocaleString()}点→${best.avgPoints.toLocaleString()}点へ伸びるため実戦価値で逆転します。`;
      } else if (widthDiff < 0) {
        msg += `${nextLabel}は打${compName}の${comp.nextStageAvgWidth}枚に対し打${bestName}は${best.nextStageAvgWidth}枚ですが、手役・打点効率で逆転します。`;
      } else {
        msg += `最終打点効率で逆転します。`;
      }
    } else if (widthDiff > 0) {
      msg += `打${bestName}の方が好形ブロックを残せるため、${nextLabel}が${comp.nextStageAvgWidth}枚→${best.nextStageAvgWidth}枚へ向上します。`;
    } else if (sh === 1 && ptsDiff > 300) {
      msg += `打${bestName}はテンパイ時の期待打点が平均${comp.avgPoints.toLocaleString()}点→${best.avgPoints.toLocaleString()}点へ伸びるため打点効率で逆転します。`;
    } else {
      msg += `${nextLabel}は打${compName}の${comp.nextStageAvgWidth}枚に対し打${bestName}は${best.nextStageAvgWidth}枚ですが、残すブロックの良形度・打点効率で打${bestName}が勝ります。`;
    }
  }

  return msg;
}

/* 6. 固定テンプレート全廃：実戦ツモ進行＆動的ブロック合成による無限生成 */
const MODE_QUEUE = [];
const RECENT_HAND_HASHES = [];

const SIMULATION_PROFILES = [
  { mode: 'sim_2s_normal',    targetSh: 2 },
  { mode: 'sim_1s_normal',    targetSh: 1 },
  { mode: 'sim_3s_normal',    targetSh: 3 },
  { mode: 'sim_1s_tanyao',    targetSh: 1 },
  { mode: 'sim_2s_yaku',      targetSh: 2 },
  { mode: 'sim_1s_sanshoku',  targetSh: 1 },
  { mode: 'sim_1s_honitsu',   targetSh: 1 },
  { mode: 'sim_1s_koutsu',    targetSh: 1 },
  { mode: 'sim_0s_multiwait', targetSh: 0 },
  { mode: 'sim_0s_menchin',   targetSh: 0 }
];

function getNextSimProfile() {
  if (MODE_QUEUE.length === 0) {
    const copy = [...SIMULATION_PROFILES];
    shuffleInPlace(copy);
    MODE_QUEUE.push(...copy);
  }
  return MODE_QUEUE.pop();
}

function shuffleInPlace(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function hasIsolatedTile(counts, doraIdx) {
  for (let i = 0; i < 34; i++) {
    if (!counts[i]) continue;
    if (i >= 27) { if (counts[i] < 2) return true; continue; }
    if (counts[i] >= 2 || i === doraIdx) continue;
    const pos = i % 9;
    const near =
      (pos >= 1 && counts[i - 1] > 0) ||
      (pos >= 2 && counts[i - 2] > 0) ||
      (pos <= 7 && counts[i + 1] > 0) ||
      (pos <= 6 && counts[i + 2] > 0);
    if (!near) return true;
  }
  return false;
}

/**
 * 3シャンテン専用：完成面子を作らず2枚ブロック（両面・カンチャン・ペンチャン・対子）を
 * ランダムに7組合成して、毎回異なる孤立牌ゼロの3シャンテン実戦配牌を生成する
 */
function simulate3ShantenHand() {
  const c = new Array(34).fill(0);
  const taatsuPool = [];
  for (const s of [0, 9, 18]) {
    for (let p = 0; p < 8; p++) taatsuPool.push([s + p, s + p + 1]);
    for (let p = 0; p < 7; p++) taatsuPool.push([s + p, s + p + 2]);
  }
  const pairPool = [];
  for (const s of [0, 9, 18]) for (let p = 0; p < 9; p++) pairPool.push(s + p);
  for (const z of [27, 28, 31, 32, 33]) pairPool.push(z);

  const numPairs = Math.random() < 0.55 ? 1 : 2;
  let total = 0;
  for (let k = 0; k < numPairs; k++) {
    const pTile = pickRandom(pairPool);
    if (c[pTile] === 0) { c[pTile] += 2; total += 2; }
  }

  while (total < 14) {
    let placed = false;
    for (let t = 0; t < 30; t++) {
      const [a, b] = pickRandom(taatsuPool);
      if (c[a] < 4 && c[b] < 4) {
        c[a]++; c[b]++;
        if (calcStandardShantenFromCounts(c) >= 3) {
          total += 2; placed = true; break;
        }
        c[a]--; c[b]--;
      }
    }
    if (!placed) return null;
  }

  if (calcStandardShantenFromCounts(c) !== 3 || hasIsolatedTile(c, -1)) return null;
  return c;
}

/**
 * 非染め手・複合多面張テンパイ専用：
 * 1〜2組のランダム完成面子を別スートに置き、残り8〜11枚を1スートの連続帯から動的ツモ進行で生成する
 */
function simulateMultiwaitTenpaiHand() {
  const suits = shuffleInPlace([0, 9, 18]);
  const s1 = suits[0], s2 = suits[1], s3 = suits[2];
  const c = new Array(34).fill(0);

  const numFixed = Math.random() < 0.5 ? 1 : 2;
  if (Math.random() < 0.8) {
    const m1 = Math.floor(Math.random() * 7);
    c[s2 + m1]++; c[s2 + m1 + 1]++; c[s2 + m1 + 2]++;
  } else {
    const k1 = Math.floor(Math.random() * 9);
    c[s2 + k1] += 3;
  }
  if (numFixed === 2) {
    const m2 = Math.floor(Math.random() * 7);
    c[s3 + m2]++; c[s3 + m2 + 1]++; c[s3 + m2 + 2]++;
  }

  const remNeed = 14 - numFixed * 3;
  const wLen = remNeed === 8 ? 6 : 7;
  const wStart = Math.floor(Math.random() * (10 - wLen));
  const wall = [];
  for (let p = wStart; p < wStart + wLen; p++) {
    for (let k = 0; k < 4; k++) wall.push(s1 + p);
  }
  shuffleInPlace(wall);

  let wIdx = 0, added = 0;
  while (added < remNeed && wIdx < wall.length) {
    const t = wall[wIdx++];
    if (c[t] < 4) { c[t]++; added++; }
  }
  if (added < remNeed) return null;

  for (let step = 0; step < 25; step++) {
    const sh = calcStandardShantenFromCounts(c);
    if (sh === 0 && !hasIsolatedTile(c, -1)) return [...c];
    if (sh < 0 || wIdx >= wall.length) return null;

    let bestD = -1, bestSc = -1e9;
    for (let d = s1; d < s1 + 9; d++) {
      if (c[d] === 0) continue;
      c[d]--;
      const shA = calcStandardShantenFromCounts(c);
      c[d]++;
      const sc = -shA * 100 + Math.random() * 20;
      if (sc > bestSc) { bestSc = sc; bestD = d; }
    }
    if (bestD === -1) return null;
    c[bestD]--;

    let drawn = false;
    while (wIdx < wall.length) {
      const t = wall[wIdx++];
      if (c[t] < 4) { c[t]++; drawn = true; break; }
    }
    if (!drawn) return null;
  }
  return null;
}

function buildWallForProfile(mode) {
  const wall = [];
  const suits = shuffleInPlace([0, 9, 18]);
  const s1 = suits[0], s2 = suits[1];
  const pushN = (tile, n) => { for (let k = 0; k < n; k++) wall.push(tile); };

  if (mode === 'sim_1s_normal' || mode === 'sim_2s_normal') {
    for (let i = 0; i < 27; i++) pushN(i, 4);
    const honors = shuffleInPlace([27, 28, 29, 30, 31, 32, 33]).slice(0, 3);
    honors.forEach(z => pushN(z, 3));
  } else if (mode === 'sim_1s_tanyao' || mode === 'sim_2s_yaku') {
    for (const s of [0, 9, 18]) {
      for (let p = 1; p <= 7; p++) pushN(s + p, 4);
      pushN(s + 0, 2);
      pushN(s + 8, 2);
    }
    if (mode === 'sim_2s_yaku' && Math.random() < 0.45) {
      pushN(pickRandom([27, 28, 31, 32, 33]), 3);
    }
  } else if (mode === 'sim_1s_sanshoku') {
    const pos = pickRandom([0, 1, 2, 3, 4, 5, 6]);
    for (let i = 0; i < 27; i++) pushN(i, 3);
    for (const s of [0, 9, 18]) {
      pushN(s + pos, 3);
      pushN(s + pos + 1, 3);
      pushN(s + pos + 2, 3);
    }
  } else if (mode === 'sim_1s_honitsu') {
    for (let p = 0; p < 9; p++) pushN(s1 + p, 4);
    const yakuhai = shuffleInPlace([27, 28, 31, 32, 33]).slice(0, 3);
    yakuhai.forEach(z => pushN(z, 4));
    const offPos = shuffleInPlace([1, 2, 3, 4, 5, 6, 7]).slice(0, 4);
    offPos.forEach(p => pushN(s2 + p, 2));
  } else if (mode === 'sim_1s_koutsu') {
    const nums = shuffleInPlace(Array.from({ length: 27 }, (_, i) => i)).slice(0, 11);
    const zTiles = shuffleInPlace([27, 28, 31, 32, 33]).slice(0, 2);
    [...nums, ...zTiles].forEach(t => pushN(t, 4));
  } else {
    for (let p = 0; p < 9; p++) pushN(s1 + p, 4);
  }

  return shuffleInPlace(wall);
}

function simulateHandFromWall(mode, targetSh) {
  if (mode === 'sim_3s_normal') return simulate3ShantenHand();
  if (mode === 'sim_0s_multiwait') return simulateMultiwaitTenpaiHand();

  const wall = buildWallForProfile(mode);
  const c = new Array(34).fill(0);
  let handLen = 0, wIdx = 0;

  while (handLen < 14 && wIdx < wall.length) {
    const t = wall[wIdx++];
    if (c[t] < 4) { c[t]++; handLen++; }
  }
  if (handLen < 14) return null;

  for (let step = 0; step < 30; step++) {
    const sh = calcStandardShantenFromCounts(c);
    if (sh === targetSh && !hasIsolatedTile(c, -1)) {
      return [...c];
    }
    if (sh < targetSh) return null;
    if (wIdx >= wall.length) return null;

    let bestD = -1, bestSc = -1e9;
    for (let d = 0; d < 34; d++) {
      if (c[d] === 0) continue;
      c[d]--;
      const shAfter = calcStandardShantenFromCounts(c);
      c[d]++;

      let isoBonus = 0;
      if (d >= 27 && c[d] === 1) {
        isoBonus = 55;
      } else if (d < 27 && c[d] === 1) {
        const pos = d % 9;
        const near =
          (pos >= 1 && c[d - 1] > 0) ||
          (pos >= 2 && c[d - 2] > 0) ||
          (pos <= 7 && c[d + 1] > 0) ||
          (pos <= 6 && c[d + 2] > 0);
        if (!near) isoBonus = 45 + (pos === 0 || pos === 8 ? 8 : 0);
      }
      const sc = -shAfter * 100 + isoBonus + Math.random() * 18;
      if (sc > bestSc) { bestSc = sc; bestD = d; }
    }
    if (bestD === -1) return null;
    c[bestD]--;

    let drawn = false;
    while (wIdx < wall.length) {
      const t = wall[wIdx++];
      if (c[t] < 4) { c[t]++; drawn = true; break; }
    }
    if (!drawn) return null;
  }
  return null;
}

function quickPassFilter(counts, doraInd, targetSh) {
  const vis = [...counts];
  vis[doraInd]++;
  const simpleCands = [];

  for (let d = 0; d < 34; d++) {
    if (counts[d] === 0) continue;
    counts[d]--;
    const shA = calcStandardShantenFromCounts(counts);
    if (shA <= targetSh) {
      let ukTiles = 0, ukTypes = 0;
      const rel = getRelevantTiles(counts);
      for (const t of rel) {
        const rem = Math.max(0, 4 - vis[t]);
        if (rem <= 0) continue;
        counts[t]++;
        if (calcStandardShantenFromCounts(counts) < shA) {
          ukTiles += rem;
          ukTypes++;
        }
        counts[t]--;
      }
      if (ukTiles > 0) simpleCands.push({ ukTiles, ukTypes, d });
    }
    counts[d]++;
  }

  if (simpleCands.length < 3) return false;
  simpleCands.sort((a, b) => b.ukTiles - a.ukTiles);
  const b0 = simpleCands[0], b1 = simpleCands[1];

  if (targetSh === 0) {
    return (b0.ukTypes >= 3 || b0.ukTiles >= 8) && (b0.ukTiles > b1.ukTiles) && (b0.ukTiles - b1.ukTiles <= 6);
  }
  return (b0.ukTiles - b1.ukTiles <= 8);
}

function buildDynamicProblemLabel(hand14, analysis) {
  const sh = analysis.currentShanten;
  const best = analysis.candidates[0];
  const tags = best.yakuSummary || [];

  const suitTotals = [0, 0, 0];
  let honorTotal = 0;
  hand14.forEach(t => { if (t < 27) suitTotals[Math.floor(t / 9)]++; else honorTotal++; });
  const maxSuit = Math.max(...suitTotals);

  if (sh === 0) {
    if (maxSuit === 14) return 'メンチン(清一色) 多面張テンパイ';
    if (maxSuit + honorTotal === 14) return 'ホンイツ(混一色) 多面待ちテンパイ';
    return '複合形 多面待ちテンパイ';
  }
  if (sh === 1) {
    if (maxSuit === 14) return 'メンチン(清一色) 1シャンテン受け入れ';
    if (maxSuit + honorTotal >= 12) return '1シャンテン 染め手・手役分岐';
    if (tags.includes('三色同順')) return '1シャンテン 三色・好形選択';
    if (tags.includes('一気通貫')) return '1シャンテン 一通・好形選択';
    if (tags.includes('三暗刻') || tags.includes('対々和')) return '1シャンテン 暗刻・対子バランス';
    if (tags.includes('断幺九') || tags.includes('平和')) return '1シャンテン 好形・手役選択';
    return '1シャンテン 複合形・受け入れ選択';
  }
  if (sh === 2) {
    if (tags.includes('三色同順') || tags.includes('一気通貫') || tags.includes('混一色含み') || tags.includes('清一色含み')) {
      return '2シャンテン→1シャンテン 手役・ブロック構想';
    }
    return '2シャンテン→1シャンテン 受け入れ・好形構想';
  }
  return '3シャンテン→2シャンテン 序盤ブロック・手役構想';
}

function tryBuildRealGameProblem(profile) {
  const { mode, targetSh } = profile;
  const counts = simulateHandFromWall(mode, targetSh);
  if (!counts) return null;

  const hand14 = [];
  for (let i = 0; i < 34; i++) for (let k = 0; k < counts[i]; k++) hand14.push(i);
  if (hand14.length !== 14) return null;

  const handHash = hand14.join(',');
  if (RECENT_HAND_HASHES.includes(handHash)) return null;

  let doraInd = -1;
  if (Math.random() < 0.55) {
    const candidateDora = pickRandom(hand14);
    const ind = getIndicatorForDora(candidateDora);
    if (counts[ind] < 4) doraInd = ind;
  }
  if (doraInd === -1) {
    const validInds = [];
    for (let i = 0; i < 34; i++) if (counts[i] < 4) validInds.push(i);
    if (!validInds.length) return null;
    doraInd = pickRandom(validInds);
  }

  if (!quickPassFilter([...counts], doraInd, targetSh)) return null;

  const roundWindIdx = 27;
  const seatWindIdx = pickRandom([27, 28, 29, 30]);
  const analysis = analyze14Hand(hand14, roundWindIdx, seatWindIdx, doraInd, mode);
  const sh = analysis.currentShanten;

  if (sh !== targetSh || analysis.candidates.length < 3) return null;

  const best = analysis.candidates[0];
  const second = analysis.candidates[1];
  const third = analysis.candidates[2];

  if (best.scoreMetric <= second.scoreMetric || isEquivalentGoodDiscard(best, second, sh)) return null;

  if (sh === 0 || mode === 'sim_0s_menchin') {
    if (best.ukeireCount <= second.ukeireCount) return null;
    if (best.ukeireCount - second.ukeireCount > 6) return null;
  } else {
    if (Math.abs(best.ukeireCount - second.ukeireCount) >= 8) return null;
    if (best.ukeireCount < second.ukeireCount - 4) return null;
    if (best.ukeireCount - third.ukeireCount >= 14) return null;
  }

  RECENT_HAND_HASHES.push(handHash);
  if (RECENT_HAND_HASHES.length > 40) RECENT_HAND_HASHES.shift();

  return {
    roundWindIdx,
    seatWindIdx,
    doraIndicatorIdx: doraInd,
    hand14,
    isCustom: false,
    problemLabel: buildDynamicProblemLabel(hand14, analysis),
    analysis
  };
}

function generateInfiniteProblem() {
  for (let round = 0; round < 20; round++) {
    const profile = getNextSimProfile();
    for (let attempt = 0; attempt < 25; attempt++) {
      const p = tryBuildRealGameProblem(profile);
      if (p) return p;
    }
  }
  const fb = [1, 2, 3, 5, 5, 10, 11, 12, 19, 20, 22, 23, 25, 26];
  const analysis = analyze14Hand(fb, 27, 28, 4, 'auto');
  return {
    roundWindIdx: 27,
    seatWindIdx: 28,
    doraIndicatorIdx: 4,
    hand14: fb,
    isCustom: false,
    problemLabel: buildDynamicProblemLabel(fb, analysis),
    analysis
  };
}

/* 7. UIコントローラ＆イベントバインディング */
const STORAGE_KEY_REVIEW = 'mahjong_nanikiru_review_v12';
const STORAGE_KEY_STATS  = 'mahjong_nanikiru_stats_v12';

const state = {
  currentProb: null,
  answered: false,
  isReviewMode: false,
  reviewQueue: [],
  totalCount: 0,
  correctCount: 0,
  streak: 0,
  customTiles: [],
  resetConfirmPending: false,
  resetConfirmTimer: null
};

const createProbId = (p) => `${p.roundWindIdx}_${p.seatWindIdx}_${p.doraIndicatorIdx}_${[...p.hand14].sort((a,b)=>a-b).join('.')}`;
const savePersistent = (k, d) => { try { localStorage.setItem(k, JSON.stringify(d)); } catch (e) {} };
const loadPersistent = (k, fb) => { try { const r = localStorage.getItem(k); return r ? JSON.parse(r) : fb; } catch (e) { return fb; } };

function isInReviewQueue(p) {
  if (!p) return false;
  const id = createProbId(p);
  return state.reviewQueue.some(item => createProbId(item) === id);
}

function refreshBookmarkButtonUI() {
  const btn = document.getElementById('btn-toggle-bookmark');
  if (!btn || !state.currentProb) return;
  if (isInReviewQueue(state.currentProb)) {
    btn.textContent = '復習リストから削除';
    btn.className = 'px-2.5 py-1 rounded-lg bg-rose-100 hover:bg-rose-200 text-rose-800 border border-rose-300 text-[11px] font-black shrink-0 transition';
  } else {
    btn.textContent = '復習リストに残す';
    btn.className = 'px-2.5 py-1 rounded-lg bg-white hover:bg-slate-100 text-slate-700 border border-slate-300 text-[11px] font-black shrink-0 transition';
  }
}

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
    revBtn.disabled = false;
    pill.classList.remove('hidden');
  } else {
    revBtn.textContent = `復習 (${cnt}問)`;
    revBtn.disabled = cnt === 0;
    revBtn.className = cnt > 0
      ? 'px-2.5 py-1 rounded-lg bg-rose-50 hover:bg-rose-100 active:scale-95 text-rose-700 font-black text-[11px] sm:text-xs border border-rose-200 whitespace-nowrap transition'
      : 'px-2.5 py-1 rounded-lg bg-slate-100 text-slate-400 font-bold text-[11px] sm:text-xs border border-slate-200 whitespace-nowrap cursor-default';
    pill.classList.add('hidden');
  }
}

function handleResetStatsClick() {
  const btn = document.getElementById('btn-reset-stats');
  if (!state.resetConfirmPending) {
    state.resetConfirmPending = true;
    btn.textContent = '本当に消す？';
    btn.className = 'px-2 py-0.5 rounded bg-rose-600 text-white border border-rose-700 text-[10px] sm:text-[11px] font-black shrink-0 transition';
    if (state.resetConfirmTimer) clearTimeout(state.resetConfirmTimer);
    state.resetConfirmTimer = setTimeout(() => {
      state.resetConfirmPending = false;
      btn.textContent = 'リセット';
      btn.className = 'px-2 py-0.5 rounded bg-white hover:bg-slate-200 active:scale-95 text-slate-600 border border-slate-300 text-[10px] sm:text-[11px] font-bold shrink-0 transition';
    }, 3000);
    return;
  }

  if (state.resetConfirmTimer) clearTimeout(state.resetConfirmTimer);
  state.resetConfirmPending = false;
  state.totalCount = 0;
  state.correctCount = 0;
  state.streak = 0;
  savePersistent(STORAGE_KEY_STATS, { totalCount: 0, correctCount: 0, streak: 0 });
  updateHeaderAndStatsUI();

  btn.textContent = 'リセット';
  btn.className = 'px-2 py-0.5 rounded bg-white hover:bg-slate-200 active:scale-95 text-slate-600 border border-slate-300 text-[10px] sm:text-[11px] font-bold shrink-0 transition';
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
    const currentId = state.currentProb ? createProbId(state.currentProb) : '';
    const pool = state.reviewQueue.length > 1
      ? state.reviewQueue.filter(item => createProbId(item) !== currentId)
      : state.reviewQueue;
    const raw = pickRandom(pool);
    const analysis = analyze14Hand(raw.hand14, raw.roundWindIdx, raw.seatWindIdx, raw.doraIndicatorIdx, raw.category || 'auto');
    if (analysis.candidates.length > 0) {
      loadProblemToUI({ ...raw, isCustom: false, analysis });
      return;
    }
  }
  loadProblemToUI(generateInfiniteProblem());
}

function handleSelectDiscard(userTile) {
  if (state.answered) return;
  state.answered = true;
  const prob = state.currentProb;
  const best = prob.analysis.candidates[0];
  const userCand = prob.analysis.candidates.find(c => c.discardTile === userTile);
  const isExactBest = userTile === best.discardTile;
  const isEquivGood = !isExactBest && isEquivalentGoodDiscard(best, userCand, prob.analysis.currentShanten);
  const isCorrect = isExactBest || isEquivGood;

  const probId = createProbId(prob);
  const statusMsg = document.getElementById('review-status-msg');

  if (!prob.isCustom) {
    state.totalCount++;
    if (isCorrect) { state.correctCount++; state.streak++; } else { state.streak = 0; }
    savePersistent(STORAGE_KEY_STATS, { totalCount: state.totalCount, correctCount: state.correctCount, streak: state.streak });

    if (!isCorrect) {
      if (!isInReviewQueue(prob)) {
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
      statusMsg.textContent = isInReviewQueue(prob) ? '復習リストに登録されています' : '復習リストに保存できます';
    }
  } else {
    statusMsg.textContent = 'カスタム手牌の解析結果（成績には計上されません）';
  }

  updateHeaderAndStatsUI();
  renderResultSection(prob, userTile, isCorrect, isEquivGood);
}

function renderResultSection(prob, userTile, isCorrect, isEquivGood = false) {
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
    vBadge.textContent = isEquivGood ? '正解 (同格良手)' : '正解';
    vTitle.textContent = isEquivGood ? `打${TILE_NAMES_JA[userTile]}も同格の良手です！` : '最善手です！';
    vUserRow.classList.add('hidden');
  } else {
    vBanner.className = 'rounded-2xl p-3.5 border-2 border-rose-500 bg-rose-50/70 shadow-sm space-y-2';
    vBadge.className = 'px-2.5 py-0.5 rounded-md bg-rose-600 text-white text-xs font-black shrink-0';
    vBadge.textContent = '不正解';
    vTitle.textContent = `最善は「打${TILE_NAMES_JA[best.discardTile]}」`;
    vUserRow.classList.remove('hidden');
    vUserAns.innerHTML = `<span class="inline-flex items-center gap-1"><span class="mini-tile-sm">${renderTileSVG(userTile)}</span><span>打 ${TILE_NAMES_JA[userTile]}</span></span>`;
  }

  refreshBookmarkButtonUI();

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
    const isEquiv = idx > 0 && isEquivalentGoodDiscard(best, cand, sh);
    const badge = idx === 0
      ? `<span class="px-1.5 py-0.5 rounded bg-emerald-600 text-white font-black text-[10px]">最善</span>`
      : isEquiv
        ? `<span class="px-1.5 py-0.5 rounded bg-emerald-100 text-emerald-800 border border-emerald-300 font-black text-[10px]">同格</span>`
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

let syncCustomPreviewFn = null;

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
  syncCustomPreviewFn = updateCustomPreview;

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
    if (state.customTiles.filter(x => x === dora).length >= 4) {
      showCustomErr(`ドラ表示牌の${TILE_NAMES_JA[dora]}が手牌に4枚含まれています（計5枚は不可）`);
      return;
    }
    const analysis = analyze14Hand(state.customTiles, 27, seat, dora, 'auto');
    if (analysis.currentShanten < 0) {
      showCustomErr('この手牌はすでにアガリ形（完成形）です');
      return;
    }
    if (!analysis.candidates.length) {
      showCustomErr('有効な打牌候補が見つかりませんでした');
      return;
    }
    document.getElementById('custom-panel').classList.add('hidden');
    clearCustomErr();
    loadProblemToUI({
      roundWindIdx: 27,
      seatWindIdx: seat,
      doraIndicatorIdx: dora,
      hand14: [...state.customTiles],
      isCustom: true,
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
      if (syncCustomPreviewFn) syncCustomPreviewFn();
    } else if (state.currentProb) {
      renderActiveHandRack(state.currentProb.hand14, (t) => handleSelectDiscard(t));
    }
  });
  document.getElementById('btn-reset-stats').addEventListener('click', handleResetStatsClick);
  document.getElementById('btn-toggle-bookmark').addEventListener('click', () => {
    const p = state.currentProb;
    if (!p) return;
    const id = createProbId(p);
    if (isInReviewQueue(p)) {
      state.reviewQueue = state.reviewQueue.filter(item => createProbId(item) !== id);
      document.getElementById('review-status-msg').textContent = '復習リストから削除しました';
    } else {
      state.reviewQueue.push({
        roundWindIdx: p.roundWindIdx,
        seatWindIdx: p.seatWindIdx,
        doraIndicatorIdx: p.doraIndicatorIdx,
        hand14: [...p.hand14],
        problemLabel: p.problemLabel,
        category: p.analysis.problemCategory
      });
      document.getElementById('review-status-msg').textContent = '📌 復習リストに保存しました';
    }
    savePersistent(STORAGE_KEY_REVIEW, state.reviewQueue);
    updateHeaderAndStatsUI();
    refreshBookmarkButtonUI();
  });

  startNextProblem();
});