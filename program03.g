#############################################################################
## tg49_onefile.g  (self-contained)
## - H-invariant subspaces of F7^7 for each H <= Sym(7) (transitive groups)
## - "24thin-like" generation on degree 49 using C7-kernel + C6 twists
## - (optional) a lightweight "cany-basic" layer (direct/diag/aug A^7 ⋊ H)
## - keying/fingerprinting + save to .g files (not CSV)
##
## Usage:
##   gap> Read("tg49_onefile.g");
##   gap> EnsureTG49_HSubspaces();                  # compute/cache
##   gap> R := RunTG49_24Thin_SaveG("keys.g","reps.g", rec(
##            modes := ["source","dest","shifted"],
##            twistType := "C6",          # "C2" or "C3" or "C6"
##            maxTwistTuples := 50000,    # cap (per H)
##            strictSize := false,
##            keyLevel := 2,
##            repGensMax := 6,
##            quiet := false
##          ));
##
## Optional combined:
##   gap> R := RunTG49_CanyAnd24Thin_SaveG("keys.g","reps.g", rec(
##            doCany := true, doThin := true,
##            cany := rec( useFull := true, useDiag := true, useAug := true ),
##            thin := rec( twistType:="C6", modes:=["source","dest","shifted"] ),
##            keyLevel := 2, repGensMax := 6, quiet := false
##          ));
#############################################################################

#############################################################################
# 0. Parameters (block size p=7, number of blocks m=7)
#############################################################################
P49 := 7;
M49 := 7;
N49 := P49 * M49;

#############################################################################
# 1. Small utilities
#############################################################################
TG49_ModP := function(x, p)
  x := x mod p;
  if x < 0 then x := x + p; fi;
  return x;
end;

TG49_InvModPrime := function(a, p)
  a := TG49_ModP(a, p);
  if a = 0 then Error("TG49_InvModPrime: a=0"); fi;
  return PowerModInt(a, p-2, p);
end;

TG49_Join := function(L, sep)
  local s, i;
  s := "";
  for i in [1..Length(L)] do
    if i > 1 then s := Concatenation(s, sep); fi;
    s := Concatenation(s, L[i]);
  od;
  return s;
end;

#############################################################################
# 2. Linear algebra over Z/pZ (no FFE, no BaseMat, no VectorSpace)
#############################################################################
TG49_RowReduceModP := function(rows, p)
  local A, m, r, c, i, k, pivotRow, inv, tmp, factor;

  if Length(rows) = 0 then return []; fi;
  m := Length(rows[1]);

  # deep mutable copy
  A := List(rows, v -> List(v, x -> TG49_ModP(x, p)));

  r := 1;  c := 1;
  while r <= Length(A) and c <= m do
    pivotRow := 0;
    for i in [r..Length(A)] do
      if A[i][c] <> 0 then pivotRow := i; break; fi;
    od;

    if pivotRow = 0 then
      c := c + 1;
      continue;
    fi;

    if pivotRow <> r then
      tmp := A[r]; A[r] := A[pivotRow]; A[pivotRow] := tmp;
    fi;

    inv := TG49_InvModPrime(A[r][c], p);
    for k in [c..m] do
      A[r][k] := TG49_ModP(A[r][k] * inv, p);
    od;

    for i in [1..Length(A)] do
      if i = r then continue; fi;
      factor := A[i][c];
      if factor <> 0 then
        for k in [c..m] do
          A[i][k] := TG49_ModP(A[i][k] - factor * A[r][k], p);
        od;
      fi;
    od;

    r := r + 1;
    c := c + 1;
  od;

  return Filtered(A, v -> ForAny(v, x -> x <> 0));
end;

TG49_BasisKey := function(B, p)
  local flat, v;
  flat := [];
  for v in B do
    Append(flat, v);
    Add(flat, -1);
  od;
  return String(flat);
end;

TG49_SumRowSpaces := function(B1, B2, p)
  return TG49_RowReduceModP(Concatenation(B1, B2), p);
end;

#############################################################################
# 3. Wreath embedding helpers (block model: 7 blocks of size 7)
#############################################################################

# Lift g in Sym(7) into block i (1..7) acting on positions of that block
TG49_LiftToBlockPerm_2 := function(g, i)
  local off, imgs, j;
  off := (i-1)*P49;
  imgs := [1..N49];
  for j in [1..P49] do
    imgs[off + j] := off + (j^g);
  od;
  return PermList(imgs);
end;

# Accept both (g,i) and (g,i,p,m) to stay compatible with older calls
TG49_LiftToBlockPerm := function(arg)
  local g, i, p_, m_, n_, off, img, k;
  if Length(arg) = 2 then
    g := arg[1];  i := arg[2];
    return TG49_LiftToBlockPerm_2(g, i);
  elif Length(arg) = 4 then
    g := arg[1];  i := arg[2];
    p_ := arg[3]; m_ := arg[4];
  else
    Error("TG49_LiftToBlockPerm: need (g,i) or (g,i,p,m)");
  fi;

  n_  := p_ * m_;
  off := (i-1) * p_;
  img := [1..n_];
  for k in [1..p_] do
    img[off+k] := off + (k ^ g);
  od;
  return PermList(img);
end;

# Block permutation lift: h in Sym(7) acts on block indices; inside-block index stays
TG49_BlockPerm_1 := function(h)
  local img, i, j, src, dst;
  img := [1..N49];
  for i in [1..M49] do
    for j in [1..P49] do
      src := (i-1)*P49 + j;
      dst := ((i^h)-1)*P49 + j;
      img[src] := dst;
    od;
  od;
  return PermList(img);
end;

# Accept both (h) and (h,p,m)
TG49_BlockPerm := function(arg)
  local h, p_, m_, img, i, j, src, dst;
  if Length(arg) = 1 then
    h := arg[1];
    return TG49_BlockPerm_1(h);
  elif Length(arg) = 3 then
    h := arg[1]; p_ := arg[2]; m_ := arg[3];
    img := [1..(p_*m_)];
    for i in [1..m_] do
      for j in [1..p_] do
        src := (i-1)*p_ + j;
        dst := ((i^h)-1)*p_ + j;
        img[src] := dst;
      od;
    od;
    return PermList(img);
  else
    Error("TG49_BlockPerm: need (h) or (h,p,m)");
  fi;
end;

TG49_BuildKH := function(K, H)
  return Group(Concatenation(
    GeneratorsOfGroup(K),
    List(GeneratorsOfGroup(H), h -> TG49_BlockPerm(h))
  ));
end;

#############################################################################
# 4. H-invariant subspaces of F_p^m for H <= Sym(m) (row-vector convention)
#############################################################################

# cache line reps for (7,7)
TG49_AllLineReps_Normalized := function(p, m)
  local reps, i, tails, tail, v, j;

  reps := [];
  for i in [1..m] do
    if i = m then
      v := List([1..m], j -> 0);
      v[i] := 1;
      Add(reps, v);
    else
      tails := Cartesian(List([1..(m-i)], j -> [0..p-1]));
      for tail in tails do
        v := List([1..m], j -> 0);
        v[i] := 1;
        for j in [1..Length(tail)] do
          v[i+j] := tail[j];
        od;
        Add(reps, v);
      od;
    fi;
  od;
  return reps;  # size=(p^m-1)/(p-1)
end;

TG49_ApplyPermToVectorModP := function(v, h, p)
  local m, w, j;
  m := Length(v);
  w := [];
  for j in [1..m] do
    Add(w, TG49_ModP(v[ j^(h^-1) ], p));
  od;
  return w;
end;

TG49_NormalizeLineRep := function(v, p)
  local i, a, inv, w;
  for i in [1..Length(v)] do
    if TG49_ModP(v[i], p) <> 0 then
      a := TG49_ModP(v[i], p);
      inv := TG49_InvModPrime(a, p);
      w := List(v, x -> TG49_ModP(x * inv, p));
      return w;
    fi;
  od;
  return fail;
end;

TG49_OrbitSpanFromLine := function(v0, H, p)
  local gens, queue, seen, B, v, key, h, w, newB;

  gens := GeneratorsOfGroup(H);
  queue := [ v0 ];
  seen := [];
  B := [];

  while Length(queue) > 0 do
    v := queue[Length(queue)];
    Unbind(queue[Length(queue)]);

    key := String(v);
    if key in seen then
      continue;
    fi;
    AddSet(seen, key);

    newB := TG49_RowReduceModP(Concatenation(B, [v]), p);
    if Length(newB) > Length(B) then
      B := newB;
    fi;

    for h in gens do
      w := TG49_ApplyPermToVectorModP(v, h, p);
      w := TG49_NormalizeLineRep(w, p);
      if w <> fail then Add(queue, w); fi;
    od;
  od;

  return rec(B := B, key := TG49_BasisKey(B, p));
end;

TG49_AllHInvSubspacesCp_Fast := function(p, m, H)
  local reps, visited, seeds, seedKeys, v, vk, span,
        spaces, keys, queue, Bnew, Bold, Bsum, ksum, snapshot ,gens, q2, s2, u, hu, t, uk;;

  if not IsBound(TG49_LineReps_7_7) then
    TG49_LineReps_7_7 := TG49_AllLineReps_Normalized(p, m);
  fi;
  reps := TG49_LineReps_7_7;

  visited := [];
  seeds := [];
  seedKeys := [];

  # collect orbit-span seeds (one per line orbit)
  for v in reps do
    vk := String(v);
    if vk in visited then
      continue;
    fi;

    span := TG49_OrbitSpanFromLine(v, H, p);

    # mark orbit as visited (<= |H| steps)
    
    gens := GeneratorsOfGroup(H);
    q2 := [v]; s2 := [];
    while Length(q2) > 0 do
      u := q2[Length(q2)];
      Unbind(q2[Length(q2)]);
      uk := String(u);
      if uk in s2 then continue; fi;
      AddSet(s2, uk);
      AddSet(visited, uk);
      for hu in gens do
        t := TG49_NormalizeLineRep(TG49_ApplyPermToVectorModP(u, hu, p), p);
        if t <> fail then Add(q2, t); fi;
      od;
    od;

    if not (span.key in seedKeys) then
      Add(seedKeys, span.key);
      Add(seeds, span.B);
    fi;
  od;

  # close under sums (queue, snapshot to avoid iterator surprises)
  spaces := ShallowCopy(seeds);
  keys := Set(List(spaces, B -> TG49_BasisKey(B, p)));
  queue := ShallowCopy(spaces);

  while Length(queue) > 0 do
    Bnew := queue[Length(queue)];
    Unbind(queue[Length(queue)]);

    snapshot := ShallowCopy(spaces);
    for Bold in snapshot do
      Bsum := TG49_SumRowSpaces(Bnew, Bold, p);
      ksum := TG49_BasisKey(Bsum, p);
      if not (ksum in keys) then
        AddSet(keys, ksum);
        Add(spaces, Bsum);
        Add(queue, Bsum);
      fi;
    od;
  od;

  # return bases (canonical reduced)
  return spaces;
end;

#############################################################################
# 5. Precompute/cache subspaces for all transitive H on 7 blocks
#############################################################################

TG49_Tid7FromOrder := function(o)
  if o = 7 then return [7,1]; fi;
  if o = 14 then return [7,2]; fi;
  if o = 21 then return [7,3]; fi;
  if o = 42 then return [7,4]; fi;
  if o = 168 then return [7,5]; fi;
  if o = 2520 then return [7,6]; fi;
  if o = 5040 then return [7,7]; fi;
  return fail;
end;

BuildTG49_HSubspaces := function(opt)
  local quiet, k, H, subs, recH, L, i, B;

  if opt = fail then opt := rec(); fi;
  quiet := false;
  if IsBound(opt.quiet) then quiet := opt.quiet; fi;

  L := [];

  for k in [1..NrTransitiveGroups(M49)] do
    H := TransitiveGroup(M49, k);
    if not quiet then
      Print("=== H = TransitiveGroup(7,", k, ")  |H|=", Size(H), " ===\n");
    fi;

    subs := TG49_AllHInvSubspacesCp_Fast(P49, M49, H);

    recH := rec(
      Hidx := k,
      Horder := Size(H),
      subs := []
    );

    for i in [1..Length(subs)] do
      B := subs[i];
      Add(recH.subs, rec(
        dim := Length(B),
        B := B,
        key := TG49_BasisKey(B, P49)
      ));
    od;

    SortBy(recH.subs, x -> x.key);
    Add(L, recH);

    if not quiet then
      Print("  invariant subspaces found: ", Length(recH.subs), "\n\n");
    fi;
  od;

  return L;
end;

EnsureTG49_HSubspaces := function(opt)
  if IsBound(TG49_HSubspaces) and IsList(TG49_HSubspaces) and Length(TG49_HSubspaces) > 0 then
    return TG49_HSubspaces;
  fi;
  TG49_HSubspaces := BuildTG49_HSubspaces(opt);
  return TG49_HSubspaces;
end;

#############################################################################
# 6. Thin kernel from a subspace B <= F7^7 using C7 generator a
#############################################################################
TG49_KFromBasis_C7 := function(a7, B)
  local gens, row, el, i, e;
  gens := [];
  for row in B do
    el := ();
    for i in [1..M49] do
      e := row[i] mod P49;
      if e <> 0 then
        el := el * TG49_LiftToBlockPerm(a7^e, i);
      fi;
    od;
    if el <> () then Add(gens, el); fi;
  od;

  if Length(gens) = 0 then
    return rec(K := Group([()]), dim := 0);
  fi;

  # B already reduced => dim = |B|
  return rec(K := Group(gens), dim := Length(B));
end;

#############################################################################
# 7. C6 twist machinery (normalizer of <(1..7)> inside Sym(7))
#############################################################################
TG49_A7Cycle := (1,2,3,4,5,6,7);
# automorphism x -> 3x on Z/7Z gives order 6 element:
# on {1..7}: 1 fixed, (2,4,3,7,5,6) is order 6 and normalizes <a>
TG49_C6Gen := (2,4,3,7,5,6);

TG49_ZeroVec7 := function()
  return List([1..M49], function(i) return 0; end);
end;

TG49_TwistVecs := function(twistType)
  # restricted family: vectors supported on {1,i} with sum 0 mod r,
  # keeps enumeration manageable and empirically matched your 25-case scaling.
  local vecs, r, exps, i, e, v;

  if twistType = "C2" then
    r := 6; exps := [3];         # order-2 element is c^3
  elif twistType = "C3" then
    r := 6; exps := [2,4];       # order-3 subgroup generated by c^2
  else
    r := 6; exps := [1,2,3,4,5]; # full C6
  fi;

  vecs := [ TG49_ZeroVec7() ];

  for i in [2..M49] do
    for e in exps do
      v := TG49_ZeroVec7();
      v[1] := (r - e) mod r;
      v[i] := e mod r;
      Add(vecs, v);
    od;
  od;

  return vecs;
end;

TG49_DiagAutFromVec := function(c6, v)
  local el, i, e;
  el := ();
  for i in [1..M49] do
    e := v[i] mod 6;
    if e <> 0 then
      el := el * TG49_LiftToBlockPerm(c6^e, i);
    fi;
  od;
  return el;
end;

TG49_TwistedBlockLift := function(h, c6, v, mode)
  local D;
  D := TG49_DiagAutFromVec(c6, v);

  if mode = "source" then
    return D * TG49_BlockPerm(h);
  elif mode = "dest" then
    return TG49_BlockPerm(h) * D;
  elif mode = "shifted" then
    return D * TG49_BlockPerm(h) * D^-1;
  else
    Error("mode must be one of: source/dest/shifted");
  fi;
end;

#############################################################################
# 8. Keying / fingerprint (no TransitiveIdentification for degree 49)
#############################################################################
TG49_GensString := function(G, maxGens)
  local sgs, gs, imgs, i, j, tmp;

  if maxGens = fail then maxGens := 8; fi;

  sgs := SmallGeneratingSet(G);
  if Length(sgs) > maxGens then
    gs := ShallowCopy(sgs{[1..maxGens]});
  else
    gs := ShallowCopy(sgs);
  fi;

  imgs := List(gs, g -> String(List([1..N49], i -> i^g)));

  for i in [1..Length(gs)-1] do
    for j in [i+1..Length(gs)] do
      if imgs[j] < imgs[i] then
        tmp := imgs[i]; imgs[i] := imgs[j]; imgs[j] := tmp;
        tmp := gs[i];   gs[i]   := gs[j];   gs[j]   := tmp;
      fi;
    od;
  od;

  return TG49_Join(List(gs, g -> String(g)), " ; ");
end;

TG49_GroupFingerprint := function(G, level, repGensMax)
  if level = fail then level := 2; fi;
  if repGensMax = fail then repGensMax := 6; fi;

  if level = 1 then
    # cheap(ish): images-string of small generating set (still reasonably strong)
    return TG49_GensString(G, repGensMax);
  else
    # stronger: same as level 1 for now (you can extend here)
    return TG49_GensString(G, repGensMax);
  fi;
end;

#############################################################################
# 9. Save results to .g files (keys + representative gens)
#############################################################################
TG49_SaveKeyRepsG := function(fnameKeys, fnameReps, R)
  local fk, fr;

  fk := OutputTextFile(fnameKeys, false);
  AppendTo(fk, "TG49_KEYS := ", String(R.keys), ";\n");
  CloseStream(fk);

  fr := OutputTextFile(fnameReps, false);
  AppendTo(fr, "TG49_REPS := ", String(R.reps), ";\n");
  CloseStream(fr);
end;

#############################################################################
# 10. 24thin-like enumeration (C7-kernel subspaces + C6 twists on block lifts)
#############################################################################
BuildCandidates49_24Thin := function(opt)
  local modes, twistType, maxTwistTuples, strictSize, keyLevel, repGensMax, quiet,
  HS, recH, H, gensH, r, vecs, tuples, tup, mode,
 total, keys, reps, seen,
 sub, B, Krec, K, dimK, sizeK, lifts, j, G, key;

  if opt = fail then opt := rec(); fi;

  modes := ["source","dest","shifted"];
  if IsBound(opt.modes) then modes := opt.modes; fi;

  twistType := "C6";
  if IsBound(opt.twistType) then twistType := opt.twistType; fi;

  maxTwistTuples := 50000;
  if IsBound(opt.maxTwistTuples) then maxTwistTuples := opt.maxTwistTuples; fi;

  strictSize := false;
  if IsBound(opt.strictSize) then strictSize := opt.strictSize; fi;

  keyLevel := 2;
  if IsBound(opt.keyLevel) then keyLevel := opt.keyLevel; fi;

  repGensMax := 6;
  if IsBound(opt.repGensMax) then repGensMax := opt.repGensMax; fi;

  quiet := false;
  if IsBound(opt.quiet) then quiet := opt.quiet; fi;

  EnsureTG49_HSubspaces(rec(quiet := true));
  HS := TG49_HSubspaces;

  total := 0;
  keys := [];
  reps := [];
  seen := [];   # set of keys (as a Set list)

  for recH in HS do
    H := TransitiveGroup(M49, recH.Hidx);
    if not quiet then
      Print("=== H = TransitiveGroup(7,", recH.Hidx, ")  |H|=", Size(H), " ===\n");
    fi;

    gensH := GeneratorsOfGroup(H);
    r := Length(gensH);

    vecs := TG49_TwistVecs(twistType);
    tuples := Tuples(vecs, r);
    if maxTwistTuples <> fail and Length(tuples) > maxTwistTuples then
      tuples := tuples{[1..maxTwistTuples]};
    fi;

    for sub in recH.subs do
      B := sub.B;
      Krec := TG49_KFromBasis_C7(TG49_A7Cycle, B);
      K := Krec.K;
      dimK := Krec.dim;
      sizeK := P49^dimK;

      for mode in modes do
        for tup in tuples do
          lifts := [];
          for j in [1..r] do
            Add(lifts, TG49_TwistedBlockLift(gensH[j], TG49_C6Gen, tup[j], mode));
          od;

          G := Group(Concatenation(GeneratorsOfGroup(K), lifts));
          total := total + 1;

          if strictSize then
            # expected for split semidirect with image exactly H and kernel size p^dim
            if Size(G) <> sizeK * Size(H) then
              continue;
            fi;
          fi;

          key := TG49_GroupFingerprint(G, keyLevel, repGensMax);
          if not (key in seen) then
            AddSet(seen, key);
            Add(keys, key);
            Add(reps, rec(
              key := key,
              Hidx := recH.Hidx,
              mode := mode,
              dimK := dimK,
              twistType := twistType,
              gens := TG49_GensString(G, repGensMax)
            ));
          fi;
        od;
      od;
    od;

    if not quiet then
      Print("  produced (counted): ", total, "    unique keys so far: ", Length(seen), "\n\n");
    fi;
  od;

  return rec(total := total, unique := Length(seen), keys := seen, reps := reps);
end;

RunTG49_24Thin_SaveG := function(fnameKeys, fnameReps, opt)
  local R;
  if opt = fail then opt := rec(); fi;
  R := BuildCandidates49_24Thin(opt);
  TG49_SaveKeyRepsG(fnameKeys, fnameReps, R);
  return R;
end;

#############################################################################
# 11. (Optional) Cany-basic for 49: build a few base kernels from A<=Sym(7)
#     This is NOT your full 25-case cany; it's a safe, self-contained baseline.
#############################################################################
CANY49_BuildBaseDiagC := function(A)
  local gensA, diagGens, g, i, el;
  gensA := GeneratorsOfGroup(A);
  diagGens := [];
  for g in gensA do
    el := ();
    for i in [1..M49] do
      el := el * TG49_LiftToBlockPerm(g, i);
    od;
    Add(diagGens, el);
  od;
  return Group(diagGens);
end;

CANY49_BuildBaseFullC := function(A)
  local gensA, fullGens, g, i;
  gensA := GeneratorsOfGroup(A);
  fullGens := [];
  for i in [1..M49] do
    for g in gensA do
      Add(fullGens, TG49_LiftToBlockPerm(g, i));
    od;
  od;
  return Group(fullGens);
end;

CANY49_BuildBaseAugC := function(A)
  # diag + "differences" against block 1 (often equals full, but cheap to build)
  local gensA, augGens, g, i, diag;
  gensA := GeneratorsOfGroup(A);
  augGens := [];

  # diag gens
  diag := GeneratorsOfGroup(CANY49_BuildBaseDiagC(A));
  Append(augGens, diag);

  # differences
  for i in [2..M49] do
    for g in gensA do
      Add(augGens, TG49_LiftToBlockPerm(g, i) * TG49_LiftToBlockPerm(g, 1)^-1);
    od;
  od;

  return Group(augGens);
end;

BuildCandidates49_CanyBasic := function(opt)
  local useFull, useDiag, useAug, keyLevel, repGensMax, quiet,
  Hs, Cs, C, As, A, Klist, K, H, G, key,
   total, seen, reps;

  if opt = fail then opt := rec(); fi;

  useFull := true; useDiag := true; useAug := true;
  if IsBound(opt.useFull) then useFull := opt.useFull; fi;
  if IsBound(opt.useDiag) then useDiag := opt.useDiag; fi;
  if IsBound(opt.useAug) then useAug := opt.useAug; fi;

  keyLevel := 2;
  if IsBound(opt.keyLevel) then keyLevel := opt.keyLevel; fi;
  repGensMax := 6;
  if IsBound(opt.repGensMax) then repGensMax := opt.repGensMax; fi;

  quiet := false;
  if IsBound(opt.quiet) then quiet := opt.quiet; fi;

  Hs := List([1..NrTransitiveGroups(M49)], k -> TransitiveGroup(M49, k));
  Cs := List([1..NrTransitiveGroups(P49)], k -> TransitiveGroup(P49, k));

  total := 0;
  seen := [];
  reps := [];

  for C in Cs do
    As := Filtered(NormalSubgroups(C), A0 -> Size(A0) > 1 and IsTransitive(A0, [1..P49]));
    if Length(As) = 0 then As := [C]; fi;

    for A in As do
      Klist := [];
      if useFull then Add(Klist, CANY49_BuildBaseFullC(A)); fi;
      if useDiag then Add(Klist, CANY49_BuildBaseDiagC(A)); fi;
      if useAug  then Add(Klist, CANY49_BuildBaseAugC(A));  fi;

      for H in Hs do
        for K in Klist do
          G := TG49_BuildKH(K, H);
          total := total + 1;

          key := TG49_GroupFingerprint(G, keyLevel, repGensMax);
          if not (key in seen) then
            AddSet(seen, key);
            Add(reps, rec(
              key := key,
              sizeA := Size(A),
              sizeH := Size(H),
              gens := TG49_GensString(G, repGensMax)
            ));
          fi;
        od;
      od;
    od;
  od;

  if not quiet then
    Print("=== CanyBasic done: total=", total, " unique=", Length(seen), " ===\n");
  fi;
  return rec(total := total, unique := Length(seen), keys := seen, reps := reps);
end;

#############################################################################
# 12. Combined runner (CanyBasic + 24Thin) and save
#############################################################################
TG49_CountMerge := function(R1, R2)
  local keys, reps, seen, x;
  keys := []; reps := []; seen := [];

  for x in R1.keys do AddSet(seen, x); od;
  for x in R2.keys do AddSet(seen, x); od;

  # reps: just concatenate; consumer can dedup by key if desired
  reps := Concatenation(R1.reps, R2.reps);

  return rec(
    total := R1.total + R2.total,
    unique := Length(seen),
    keys := seen,
    reps := reps
  );
end;

RunTG49_CanyAnd24Thin_SaveG := function(fnameKeys, fnameReps, opt)
  local doCany, doThin, optCany, optThin, keyLevel, repGensMax, quiet,
  Rcan, Rthin, R;

  if opt = fail then opt := rec(); fi;

  doCany := true; doThin := true;
  if IsBound(opt.doCany) then doCany := opt.doCany; fi;
  if IsBound(opt.doThin) then doThin := opt.doThin; fi;

  optCany := rec();
  if IsBound(opt.cany) then optCany := opt.cany; fi;

  optThin := rec();
  if IsBound(opt.thin) then optThin := opt.thin; fi;

  keyLevel := 2;
  if IsBound(opt.keyLevel) then keyLevel := opt.keyLevel; fi;
  repGensMax := 6;
  if IsBound(opt.repGensMax) then repGensMax := opt.repGensMax; fi;

  quiet := false;
  if IsBound(opt.quiet) then quiet := opt.quiet; fi;

  Rcan := rec(total:=0, unique:=0, keys:=[], reps:=[]);
  Rthin := rec(total:=0, unique:=0, keys:=[], reps:=[]);

  if doCany then
    optCany.keyLevel := keyLevel;
    optCany.repGensMax := repGensMax;
    optCany.quiet := quiet;
    Rcan := BuildCandidates49_CanyBasic(optCany);
  fi;

  if doThin then
    optThin.keyLevel := keyLevel;
    optThin.repGensMax := repGensMax;
    optThin.quiet := quiet;
    Rthin := BuildCandidates49_24Thin(optThin);
  fi;

  R := TG49_CountMerge(Rcan, Rthin);
  TG49_SaveKeyRepsG(fnameKeys, fnameReps, R);

  if not quiet then
    Print("=== Combined: total=", R.total, " unique=", R.unique, " ===\n");
  fi;

  return R;
end;

#############################################################################
# End of file
#############################################################################
#############################################################################
# PATCH: no-argument runners (defaults baked in)
# Paste this at the very end of tg49_onefile.g
#############################################################################

# default filenames
TG49_DefaultKeysFile := "tg49_keys.g";
TG49_DefaultRepsFile := "tg49_reps.g";

# default opts for 24thin
TG49_DefaultThinOpt := rec(
  modes := ["source","dest","shifted"],
  twistType := "C6",          # "C2" / "C3" / "C6"
  maxTwistTuples := 50000,    # cap per H
  strictSize := false,
  keyLevel := 2,
  repGensMax := 6,
  quiet := false
);

# default opts for combined
TG49_DefaultCombinedOpt := rec(
  doCany := true,
  doThin := true,
  cany := rec( useFull := true, useDiag := true, useAug := true ),
  thin := rec(
    modes := ["source","dest","shifted"],
    twistType := "C6",
    maxTwistTuples := 50000,
    strictSize := false
  ),
  keyLevel := 2,
  repGensMax := 6,
  quiet := false
);

# ---- no-arg: build only (no save)
RunTG49_24Thin := function()
  return BuildCandidates49_24Thin(ShallowCopy(TG49_DefaultThinOpt));
end;

# ---- no-arg: build + save to default .g files
RunTG49_24Thin_SaveG := function()
  return RunTG49_24Thin_SaveG(
    TG49_DefaultKeysFile, TG49_DefaultRepsFile,
    ShallowCopy(TG49_DefaultThinOpt)
  );
end;

# ---- no-arg: combined + save to default .g files
RunTG49_CanyAnd24Thin_SaveG1 := function()
  return RunTG49_CanyAnd24Thin_SaveG(
    TG49_DefaultKeysFile, TG49_DefaultRepsFile,
    ShallowCopy(TG49_DefaultCombinedOpt)
  );
end;

#############################################################################
# Usage:
#   gap> Read("tg49_onefile.g");
#   gap> EnsureTG49_HSubspaces();
#   gap> R := RunTG49_24Thin();              # no save
#   gap> R := RunTG49_24Thin_SaveG();        # saves tg49_keys.g / tg49_reps.g
#   gap> R := RunTG49_CanyAnd24Thin_SaveG(); # saves tg49_keys.g / tg49_reps.g
#############################################################################
