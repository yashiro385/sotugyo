#############################################################################
# 
#
# 
# 目的:
#   - p^2 次 (例: 25, 49) の Hulpke 型「M→W→N→K→(K/M 可解なら補群列挙)」を回す
#   - 特に
#       (1) p' 側（とくに 2 側）混ぜ方を強化（Sylow2 の全生成元 + パターン）
#       (2) PCore(A,p)=1 の場合の M 候補を増やす（diag/aug/subdirect 系）
#
#############################################################################

# ---- packages ----
if LoadPackage("transgrp") <> true then
  Error("transgrp package is required (for TransitiveGroup / TransitiveIdentification).");
fi;
# MeatAxe は p>=7 で必須（p=5 は brute fallback 可）
if IsBoundGlobal("MTX") then
  # ok
else
  # attempt load
  LoadPackage("meataxe");
fi;

#############################################################################
# 基本ユーティリティ
#############################################################################

HK_SortBySecond := function(L)
  Sort(L, function(a,b) return a[2] < b[2]; end);
end;

HK_PrintTIDList := function(tids, perLine)
  local i;
  if perLine = fail then perLine := 12; fi;
  for i in [1..Length(tids)] do
    Print(tids[i]);
    if i < Length(tids) then
      Print(", ");
    fi;
    if (i mod perLine) = 0 then
      Print("\n");
    fi;
  od;
  if (Length(tids) mod perLine) <> 0 then
    Print("\n");
  fi;
end;

HK_NormalizeGroupN := function(G, n)
  local gens, g;
  gens := [];
  for g in GeneratorsOfGroup(G) do
    Add(gens, Permutation(g, [1..n]));
  od;
  if Length(gens)=0 then
    return Group(());
  fi;
  return Group(gens);
end;

HK_TIDOfGroup := function(G, n)
  local k;
  if not IsTransitive(G, [1..n]) then
    return fail;
  fi;
  k := TransitiveIdentification(G);
  if IsInt(k) and k > 0 then
    return [n, k];
  fi;
  return fail;
end;

HK_UniqueTIDsFromScans := function(scans, p)
  local n, tids, oneU, oneA, r, G, tid;
  n := p*p;
  tids := [];
  for oneU in scans do
    for oneA in oneU.Aruns do
      for r in oneA.results do
        if IsBound(r.lifts) then
          for G in r.lifts do
            tid := HK_TIDOfGroup(G, n);
            if tid <> fail then
              Add(tids, tid);
            fi;
          od;
        fi;
      od;
    od;
  od;
  tids := Set(tids);
  HK_SortBySecond(tids);
  return tids;
end;

#############################################################################
# 標準ブロック (p^2)
#############################################################################

HK_StandardBlocks := function(p)
  local blocks, i, a, b;
  blocks := [];
  for i in [1..p] do
    a := (i-1)*p + 1;
    b := i*p;
    Add(blocks, Set([a..b]));
  od;
  return blocks;
end;

HK_BlockImage := function(block, g)
  return Set(List(block, x -> x^g));
end;

HK_BlockIndex := function(blocks, b)
  local i;
  for i in [1..Length(blocks)] do
    if blocks[i] = b then
      return i;
    fi;
  od;
  return fail;
end;

HK_BlockPermOnBlocks := function(blocks, g)
  local m, img, i, bi;
  m := Length(blocks);
  img := [];
  for i in [1..m] do
    bi := HK_BlockIndex(blocks, HK_BlockImage(blocks[i], g));
    if bi = fail then
      Error("block action not well-defined for given blocks");
    fi;
    img[i] := bi;
  od;
  return PermList(img);
end;

HK_BlockActionHom := function(G, p, blocks)
  local S, gens, imgs, g;
  S := SymmetricGroup(p);
  gens := GeneratorsOfGroup(G);
  imgs := [];
  for g in gens do
    Add(imgs, HK_BlockPermOnBlocks(blocks, g));
  od;
  return GroupHomomorphismByImages(G, S, gens, imgs);
end;

#############################################################################
# 埋め込み: Sym(p) の元を p^2 上の「特定ブロック」へ
#############################################################################

HK_EmbedInBlock := function(p, a, i)
  local n, img, j, pt, jp;
  n := p*p;
  img := [1..n];
  for j in [1..p] do
    pt := (i-1)*p + j;
    jp := j^a;
    img[pt] := (i-1)*p + jp;
  od;
  return PermList(img);
end;

HK_BlockPerm := function(p, sigma)
  # ブロック i を sigma で動かし、ブロック内位置 j は固定
  local n, img, i, j, pt, it;
  n := p*p;
  img := [1..n];
  for i in [1..p] do
    it := i^sigma;
    for j in [1..p] do
      pt := (i-1)*p + j;
      img[pt] := (it-1)*p + j;
    od;
  od;
  return PermList(img);
end;

HK_EmbedGroupAllBlocks := function(p, B)
  local gensB, gens, b, i;
  gensB := GeneratorsOfGroup(B);
  gens := [];
  for i in [1..p] do
    for b in gensB do
      Add(gens, HK_EmbedInBlock(p, b, i));
    od;
  od;
  if Length(gens)=0 then
    return Group(());
  fi;
  return Group(gens);
end;

HK_EmbedDiagFromGroup := function(p, B)
  local gensB, out, b, g, i;
  gensB := GeneratorsOfGroup(B);
  out := [];
  for b in gensB do
    g := ();
    for i in [1..p] do
      g := g * HK_EmbedInBlock(p, b, i);
    od;
    if g <> () then Add(out, g); fi;
  od;
  return out;
end;

HK_EmbedAugFromGroup := function(p, B)
  local gensB, out, b, i, g;
  gensB := GeneratorsOfGroup(B);
  out := [];
  for b in gensB do
    for i in [1..p-1] do
      g := HK_EmbedInBlock(p, b, i) * (HK_EmbedInBlock(p, b, p)^-1);
      if g <> () then Add(out, g); fi;
    od;
  od;
  return out;
end;

#############################################################################
# Wreath overgroup W の明示構成（安全版）
#   W := < C^p, Sym(p) (block perm) >
#   ここで C := N_{Sym(p)}(A) （軽くしたい場合）
#############################################################################

HK_WreathOvergroupA := function(p, A, opts)
  local baseMode, C, baseGens, topGens, sig, W;

  if opts = fail or not IsRecord(opts) then opts := rec(); fi;
  baseMode := "NormA";
  if IsBound(opts.baseMode) then baseMode := opts.baseMode; fi;

  if baseMode = "Sym" then
    C := SymmetricGroup(p);
  else
    C := Normalizer(SymmetricGroup(p), A);
  fi;

  baseGens := [];
  for sig in GeneratorsOfGroup(C) do
    # 各ブロックに同じ sig を入れる生成元群（C^p）
    baseGens := Concatenation(baseGens,
                              List([1..p], i -> HK_EmbedInBlock(p, sig, i)));
  od;

  topGens := [];
  for sig in GeneratorsOfGroup(SymmetricGroup(p)) do
    Add(topGens, HK_BlockPerm(p, sig));
  od;

  W := Group(Concatenation(baseGens, topGens));
  W := HK_NormalizeGroupN(W, p*p);
  return rec(C:=C, W:=W);
end;

#############################################################################
# PCore(A,p) 由来 base (C_p)^p
#############################################################################

HK_BaseFromPCore := function(p, A)
  local P, genP, baseGens, i;
  P := PCore(A, p);
  if Size(P)=1 then
    return rec(P:=P, genP:=fail, baseGens:=[]);
  fi;
  genP := GeneratorsOfGroup(P)[1];
  baseGens := [];
  for i in [1..p] do
    Add(baseGens, HK_EmbedInBlock(p, genP, i));
  od;
  return rec(P:=P, genP:=genP, baseGens:=baseGens);
end;

HK_SubgroupFromVectors := function(baseGens, vecs, p)
  local gens, v, i, e, g;
  gens := [];
  for v in vecs do
    g := ();
    for i in [1..Length(baseGens)] do
      e := IntFFE(v[i]);   # 0..p-1
      if e <> 0 then
        g := g * (baseGens[i]^e);
      fi;
    od;
    if g <> () then Add(gens, g); fi;
  od;
  if Length(gens)=0 then
    return Group(());
  fi;
  return Group(gens);
end;

#############################################################################
# U-invariant subspaces in GF(p)^p から Mp を作る
#   - p=5 は brute fallback 可
#   - p>=7 は MeatAxe (MTX.BasesSubmodules) 必須
#############################################################################

HK_HasMTX := function()
  return IsBoundGlobal("MTX") and IsBound(MTX.BasesSubmodules);
end;

HK_InvariantSubspaces_pcore := function(p, U, baseGens, opts)
  local F, mats, g, modd, out, maxSub,V, subs, S, basis, ok, u, Mu, imgv, w, dim, Mp,bases, b;

  if opts = fail or not IsRecord(opts) then opts := rec(); fi;
  F := GF(p);

  mats := [];
  for g in GeneratorsOfGroup(U) do
    Add(mats, PermutationMat(g, p, F));
  od;
  modd := GModuleByMats(mats, F);

  out := [];
  maxSub := fail;
  if IsBound(opts.maxSubmodules) then maxSub := opts.maxSubmodules; fi;

  if HK_HasMTX() then
    bases := MTX.BasesSubmodules(modd);
    for b in bases do
      dim := Length(b);
      Mp := HK_SubgroupFromVectors(baseGens, b, p);
      Add(out, rec(dim:=dim, basis:=b, Mp:=Mp));
      if maxSub <> fail and Length(out) >= maxSub then break; fi;
    od;
    return out;
  fi;

  # brute fallback (p=5 推奨。p>=7 は不可)
  if p >= 7 then
    Error("MTX (MeatAxe) not available; cannot enumerate invariant subspaces for p>=7.");
  fi;

  V := VectorSpace(F, IdentityMat(p, F));
  subs := Subspaces(V);

  for S in subs do
    basis := BasisVectors(Basis(S));
    ok := true;

    for u in GeneratorsOfGroup(U) do
      Mu := PermutationMat(u, p, F);
      for imgv in basis do
        w := imgv * Mu;
        if not w in S then
          ok := false;
          break;
        fi;
      od;
      if not ok then break; fi;
    od;

    if ok then
      dim := Dimension(S);
      Mp := HK_SubgroupFromVectors(baseGens, basis, p);
      Add(out, rec(dim:=dim, basis:=basis, Mp:=Mp));
      if maxSub <> fail and Length(out) >= maxSub then break; fi;
    fi;
  od;

  return out;
end;

#############################################################################
# p' 側混ぜ候補（特に Sylow2(D)）
#   D := A/P (P=PCore(A,p))。P=1 のとき D=A。
#   - Sylow2(D) の生成元全てを使う
#   - full/diag/aug/mask + (h, involution) の混合パターン
#############################################################################

HK_InvolutionFrom := function(h)
  local o;
  o := Order(h);
  if o mod 2 <> 0 then return fail; fi;
  return h^(QuoInt(o, 2));
end;

HK_pprime2_GenLists := function(p, A, P, opts)
  local out, D, pi, S2, gens2D, genD, h, modes, mode,i, gens, gdiag, gaug, mask, bits, inv, invok, maxL;

  if opts = fail or not IsRecord(opts) then opts := rec(); fi;
  out := [];

  # D and lifting
  if Size(P)=1 then
    D := A;
    pi := fail;
  else
    pi := NaturalHomomorphismByNormalSubgroup(A, P);
    D := Image(pi);
  fi;

  Add(out, rec(label:="none", gens:=[]));

  S2 := SylowSubgroup(D, 2);
  gens2D := GeneratorsOfGroup(S2);

  maxL := fail;
  if IsBound(opts.maxPprimeLists) then maxL := opts.maxPprimeLists; fi;

  modes := ["full","diag","aug"];
  if IsBound(opts.pprimeModes) and IsList(opts.pprimeModes) then
    modes := opts.pprimeModes;
  fi;

  for genD in gens2D do
    if Size(P)=1 then
      h := genD;
    else
      h := PreImagesRepresentative(pi, genD);
    fi;

    for mode in modes do
      if mode = "full" then
        gens := [];
        for i in [1..p] do
          Add(gens, HK_EmbedInBlock(p, h, i));
        od;
        Add(out, rec(label:=Concatenation("Syl2:full|ord=", String(Order(h))), gens:=gens));

      elif mode = "diag" then
        gdiag := ();
        for i in [1..p] do
          gdiag := gdiag * HK_EmbedInBlock(p, h, i);
        od;
        Add(out, rec(label:=Concatenation("Syl2:diag|ord=", String(Order(h))), gens:=[gdiag]));

      elif mode = "aug" then
        gens := [];
        for i in [1..p-1] do
          gaug := HK_EmbedInBlock(p, h, i) * (HK_EmbedInBlock(p, h, p)^-1);
          Add(gens, gaug);
        od;
        Add(out, rec(label:=Concatenation("Syl2:aug|ord=", String(Order(h))), gens:=gens));
      fi;

      if maxL <> fail and Length(out) >= maxL then
        return out;
      fi;
    od;

    # masks (deterministic) : 2^p-1 patterns
    if IsBound(opts.pprimeMasks) and opts.pprimeMasks = true then
      for mask in [1..(2^p - 1)] do
        gens := [];
        bits := mask;
        for i in [1..p] do
          if (bits mod 2) = 1 then
            Add(gens, HK_EmbedInBlock(p, h, i));
          fi;
          bits := QuoInt(bits, 2);
        od;
        Add(out, rec(label:=Concatenation("Syl2:mask#", String(mask), "|ord=", String(Order(h))), gens:=gens));
        if maxL <> fail and Length(out) >= maxL then
          return out;
        fi;
      od;
    fi;

    # "one involution block" pattern
    inv := HK_InvolutionFrom(h);
    invok := (inv <> fail and inv <> ());
    if invok then
      for i in [1..p] do
        gens := [];
        for mask in [1..p] do
          if mask = i then
            Add(gens, HK_EmbedInBlock(p, inv, mask));
          else
            Add(gens, HK_EmbedInBlock(p, h, mask));
          fi;
        od;
        Add(out, rec(label:=Concatenation("Syl2:oneInv#", String(i), "|ordh=", String(Order(h))), gens:=gens));
        if maxL <> fail and Length(out) >= maxL then
          return out;
        fi;
      od;
    fi;

  od;

  # also include "use all Sylow2 gens simultaneously" in each mode
  if Length(gens2D) > 1 then
    gens := [];
    for genD in gens2D do
      if Size(P)=1 then h := genD; else h := PreImagesRepresentative(pi, genD); fi;
      for i in [1..p] do Add(gens, HK_EmbedInBlock(p, h, i)); od;
    od;
    Add(out, rec(label:="Syl2:ALLgens|full", gens:=gens));

    gdiag := ();
    for genD in gens2D do
      if Size(P)=1 then h := genD; else h := PreImagesRepresentative(pi, genD); fi;
      for i in [1..p] do gdiag := gdiag * HK_EmbedInBlock(p, h, i); od;
    od;
    Add(out, rec(label:="Syl2:ALLgens|diag", gens:=[gdiag]));
  fi;

  return out;
end;

#############################################################################
# M 候補列挙（強化版）
#   - Size(P)=1 でも diag/aug/subdirect 風を追加
#   - Size(P)>1 では Mp (U-invariant subspace) + p' mixing を合成
#############################################################################

HK_MCandidates_Ap := function(p, A, U, opts)
  local out, Pdata, P, baseGens, subs, pprimeLists, s, mp, pmode, M,Ader, N, gensN, gL;

  if opts = fail or not IsRecord(opts) then opts := rec(); fi;
  out := [];

  Pdata := HK_BaseFromPCore(p, A);
  P := Pdata.P;

  if Size(P)=1 then
    # PCore=1: p-core 由来の Mp は無い。代わりに p' 側 subdirect を M として試す。
    Add(out, rec(label:="M=1", M:=Group(()), MpDim:="NA"));

    # diag(A), aug(A)
    gL := HK_EmbedDiagFromGroup(p, A);
    if Length(gL)>0 then
      Add(out, rec(label:="M=diag(A)", M:=Group(gL), MpDim:="NA"));
    fi;

    gL := HK_EmbedAugFromGroup(p, A);
    if Length(gL)>0 then
      Add(out, rec(label:="M=aug(A)", M:=Group(gL), MpDim:="NA"));
    fi;

    # A^p
    Add(out, rec(label:="M=A^p", M:=HK_EmbedGroupAllBlocks(p, A), MpDim:="NA"));

    # also use A' if proper (S5 -> A5)
    Ader := DerivedSubgroup(A);
    if Size(Ader) > 1 and Size(Ader) < Size(A) then
      gL := HK_EmbedDiagFromGroup(p, Ader);
      if Length(gL)>0 then
        Add(out, rec(label:="M=diag(A')", M:=Group(gL), MpDim:="NA"));
      fi;

      gL := HK_EmbedAugFromGroup(p, Ader);
      if Length(gL)>0 then
        Add(out, rec(label:="M=aug(A')", M:=Group(gL), MpDim:="NA"));
      fi;

      Add(out, rec(label:="M=(A')^p", M:=HK_EmbedGroupAllBlocks(p, Ader), MpDim:="NA"));
    fi;

    return out;
  fi;

  baseGens := Pdata.baseGens;

  subs := HK_InvariantSubspaces_pcore(p, U, baseGens, opts);
  pprimeLists := HK_pprime2_GenLists(p, A, P, opts);

  for s in subs do
    mp := s.Mp;
    for pmode in pprimeLists do
      if Length(pmode.gens)=0 then
        M := mp;
      else
        M := ClosureGroup(mp, pmode.gens);
      fi;
      Add(out, rec(
        label := Concatenation("MpDim=", String(s.dim), "|pprime2=", pmode.label),
        M := M,
        MpDim := s.dim,
        Mp := mp,
        pprime := pmode.label
      ));
      if IsBound(opts.maxMsTotal) and IsInt(opts.maxMsTotal) and Length(out) >= opts.maxMsTotal then
        return out;
      fi;
    od;
  od;

  return out;
end;

#############################################################################
# 1つの M を解析: W, N, blocks, U, K, Q, (K/M 可解なら補群列挙)
#############################################################################

HK_AnalyzeOneM := function(p, A, M, U, opts)
  local n, blocks, Wrec, W, N, hom, im, okU, res,K, Q, piM, Qbar, Kbar, solv, comps, c, L, lifts,maxComp, maxLifts;

  if opts = fail or not IsRecord(opts) then opts := rec(); fi;

  n := p*p;
  blocks := HK_StandardBlocks(p);

  Wrec := HK_WreathOvergroupA(p, A, opts);
  W := Wrec.W;

  if not IsSubgroup(W, M) then
    # M が W に入らない場合はこの枝では扱えない（W を Sym にする等で回避）
    return rec(p:=p, n:=n, A:=A, M:=M, W:=W, blocks:=blocks, U:=U,
               hasU:=false, reason:="M not subgroup of chosen W");
  fi;

  N := Normalizer(W, M);
  N := HK_NormalizeGroupN(N, n);

  hom := HK_BlockActionHom(N, p, blocks);
  im := Image(hom);

  # 重要: U <= im の判定（順序に注意）
  okU := IsSubgroup(im, U);

  res := rec(
    p:=p, n:=n,
    A:=A, M:=M, W:=W, N:=N,
    blocks:=blocks, U:=U,
    hom:=hom, image:=im, hasU:=okU,
    ordM:=Size(M), ordW:=Size(W), ordN:=Size(N)
  );

  if not okU then
    return res;
  fi;

  K := Kernel(hom);
  Q := PreImage(hom, U);

  res.K := K;
  res.Q := Q;
  res.ordK := Size(K);
  res.ordQ := Size(Q);

  if not (IsBound(opts.doComplements) and opts.doComplements = true) then
    return res;
  fi;

  # complement enumeration in Qbar := Q/M, for Kbar := K/M
  if not IsNormal(Q, M) then
    res.complementsError := "M is not normal in Q (skip complements)";
    return res;
  fi;

  piM := NaturalHomomorphismByNormalSubgroup(Q, M);
  Qbar := Image(piM);
  Kbar := Image(piM, K);

  res.ordQbar := Size(Qbar);
  res.ordKbar := Size(Kbar);

  solv := IsSolvableGroup(Kbar);
  res.KbarSolvable := solv;

  if not solv then
    res.numComplements := 0;
    res.lifts := [];
    res.numLiftsTransitive := 0;
    return res;
  fi;

  maxComp := fail;
  if IsBound(opts.maxComplements) then maxComp := opts.maxComplements; fi;

  comps := ComplementClassesRepresentatives(Qbar, Kbar);
  if maxComp <> fail and Length(comps) > maxComp then
    comps := comps{[1..maxComp]};
  fi;

  res.numComplements := Length(comps);

  lifts := [];
  maxLifts := fail;
  if IsBound(opts.maxLifts) then maxLifts := opts.maxLifts; fi;

  for c in comps do
    L := PreImage(piM, c);
    L := HK_NormalizeGroupN(L, n);
    if IsTransitive(L, [1..n]) then
      Add(lifts, L);
      if maxLifts <> fail and Length(lifts) >= maxLifts then
        break;
      fi;
    fi;
  od;

  res.lifts := lifts;
  res.numLiftsTransitive := Length(lifts);
  return res;
end;



TG49_NormalizeGroupN := function(G, n)
  local gens, g;
  gens := [];
  for g in GeneratorsOfGroup(G) do
    Add(gens, Permutation(g, [1..n]));
  od;
  if Length(gens) = 0 then
    return Group(());
  fi;
  return Group(gens);
end;

TG49_GroupToRec := function(G, n)
  local Gn, gens;
  Gn := TG49_NormalizeGroupN(G, n);
  gens := List(GeneratorsOfGroup(Gn), g -> Permutation(g, [1..n]));
  return rec(
    ordG  := Size(Gn),
    sizeG := Size(Gn),
    gens  := gens,
    generator := gens    # メモリ上の rec では alias を持たせる（出力側は後で付与）
  );
end;

TG49_CollectGroupsFromScans := function(scans)
  local Gs, one, r;
  Gs := [];

  if scans = fail then
    return Gs;
  fi;

  if IsGroup(scans) then
    return [scans];
  fi;

  if IsList(scans) then
    for one in scans do
      if IsGroup(one) then
        Add(Gs, one);
      elif IsRecord(one) and IsBound(one.results) then
        for r in one.results do
          if IsBound(r.lifts) and IsList(r.lifts) then
            Append(Gs, r.lifts);
          fi;
        od;
      elif IsRecord(one) and IsBound(one.lifts) and IsList(one.lifts) then
        Append(Gs, one.lifts);
      fi;
    od;
    return Gs;
  fi;

  if IsRecord(scans) and IsBound(scans.results) then
    for r in scans.results do
      if IsBound(r.lifts) and IsList(r.lifts) then
        Append(Gs, r.lifts);
      fi;
    od;
    return Gs;
  fi;

  return Gs;
end;

TG49_SaveGroupRecsG := function(outFile, GsOrScans, opts)
  local n, Gs, recs, i, f, r, gens, j, s;

  if opts = fail or not IsRecord(opts) then opts := rec(); fi;

  n := 49;
  if IsBound(opts.n) then n := opts.n; fi;

  # groups 抽出
  Gs := TG49_CollectGroupsFromScans(GsOrScans);

  # 全部 rec 化（重複除去はしない：もれなく保存）
  recs := [];
  for i in [1..Length(Gs)] do
    Add(recs, TG49_GroupToRec(Gs[i], n));
  od;

  # 書き出し
  f := OutputTextFile(outFile, false);

  AppendTo(f, "#############################################################################\n");
  AppendTo(f, "# ", outFile, "\n");
  AppendTo(f, "# auto-generated by TG49_SaveGroupRecsG\n");
  AppendTo(f, "#############################################################################\n\n");

  AppendTo(f, "TG49_B_RECS := [\n");

  for i in [1..Length(recs)] do
    r := recs[i];
    gens := r.gens;

    AppendTo(f, "  rec(\n");
    AppendTo(f, "    ordG  := ", String(r.ordG), ",\n");
    AppendTo(f, "    sizeG := ", String(r.sizeG), ",\n");
    AppendTo(f, "    gens  := [\n");

    for j in [1..Length(gens)] do
      s := String(gens[j]);
      if j < Length(gens) then
        AppendTo(f, "      ", s, ",\n");
      else
        AppendTo(f, "      ", s, "\n");
      fi;
    od;

    AppendTo(f, "    ]\n");
    AppendTo(f, "  )");
    if i < Length(recs) then
      AppendTo(f, ",\n\n");
    else
      AppendTo(f, "\n");
    fi;
  od;

  AppendTo(f, "];\n\n");
  AppendTo(f, "for r in TG49_B_RECS do r.generator := r.gens; od;\n");
  AppendTo(f, "TG49_B_RECS_LEN := Length(TG49_B_RECS);\n");

  CloseStream(f);

  Print("Wrote: ", outFile, "\n");
  Print("Records: ", Length(recs), "\n");

  return recs;
end;










