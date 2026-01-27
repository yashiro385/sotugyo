#############################################################################
# tg25_fill_1234_mtx_twist.g  (GAP 4.15.1)
#
# One file / functions separated / one-pass run:
#   (1) GF(5)^5 permutation module: H-invariant subspaces (MTX or brute)
#       -> build K ≤ C5^5, then G = <K, Top(H)>
#   (2) C2^5 twist layer: H-invariant subspaces of GF(2)^5 (MTX or brute)
#       -> build E ≤ <inv_i>, then G = <C5^5, E, Top(H)>
#   (3) C4^5 diagonal layer: H-invariant subgroups in <mul2_i>
#       using GF(2) subspaces + ratio subgroup (C4^4)
#       -> G = <C5^5, D, (optional E), Top(H)>
#   (4) "24thin-style" twist on quotient W = GF(5)^5 / U
#       for each H-invariant U, compute H^1(H, W) via Schreier constraints
#       and twist lifts of generators by translation parts (NO fp-groups).
#
# Notes:
# - MTX.InvariantSubmodules は使いません（manual に無い）:
#   MTX.BasesSubmodules を使えるならそれを使い、無ければ brute fallback。
# - RankMat/BaseMat/NullspaceMat は “matrix object” が必要なので Matrix(F,...) を必ず挟みます。
#
# Usage:
#   Read("tg25_fill_1234_mtx_twist.g");;
#   rep := TG25_Run_Fill1234_MTX(rec(
#     knownTIDs := [],
#     do1 := true, do2 := true, do3 := true, do4 := true,
#     doDiagWithInv := true,
#     twistMaxReps := 5,        # cap per (H,U)
#     twistSkipZero := true
#   ));
#
# Optional: prevent autorun at file load:
#   TG25_NO_AUTORUN := true;;
#   Read("tg25_fill_1234_mtx_twist.g");;
#############################################################################
TG25_NO_AUTORUN := true;;
#############################################################################
# Package (MeatAxe)
#############################################################################


#############################################################################
# Helpers: normalize rows / matrix-object rank & nullspace
#############################################################################
TG25_RowsAsPlainLists := function(rows, d)
  return List(rows, r -> List([1..d], i -> r[i]));
end;

TG25_RankRows := function(F, rows, d)
  if rows = fail or not IsList(rows) or Length(rows)=0 then
    return 0;
  fi;
  return RankMat(Matrix(F, TG25_RowsAsPlainLists(rows, d)));
end;
TG25_StdBasisVec := function(F, n, i)
  return List([1..n], function(j)
    if j = i then return One(F); else return Zero(F); fi;
  end);
end;
TG25_NullspaceRows := function(F, eqRows, n)
  local N;
  if eqRows = fail or not IsList(eqRows) or Length(eqRows)=0 then
    return [];   # caller handles "no equations" separately
  fi;
  N := NullspaceMat(Matrix(F, TG25_RowsAsPlainLists(eqRows, n)));
  return TG25_RowsAsPlainLists(N, n);
end;

#############################################################################
# Z_p x Z_p model (points 0..p^2-1 encoded by (i,j), 0<=i,j<p)
#############################################################################
TG25_PermFromMapPair := function(p, fpair)
  local img, x, i, j, ij, kl;
  img := [];
  for x in [0..p*p-1] do
    i := x mod p;
    j := QuoInt(x, p);
    ij := [i, j];
    kl := fpair(ij);
    Add(img, kl[1] + kl[2]*p + 1);
  od;
  return PermList(img);
end;

TG25_LiftBlocks := function(p, h)
  return TG25_PermFromMapPair(p,
    function(ij)
      local i, j, ip;
      i := ij[1]; j := ij[2];
      ip := (i+1) ^ h;
      return [ip-1, j];
    end
  );
end;

TG25_LiftWithin := function(p, sig, i0)
  return TG25_PermFromMapPair(p,
    function(ij)
      local i, j, jp;
      i := ij[1]; j := ij[2];
      if i <> i0 then return ij; fi;
      jp := (j+1) ^ sig;
      return [i, jp-1];
    end
  );
end;

TG25_WithinPerm_Inversion := function(p)
  return PermList(List([0..p-1], j -> ((-j) mod p) + 1));
end;

TG25_WithinPerm_Mul2 := function(p)
  return PermList(List([0..p-1], j -> ((2*j) mod p) + 1));
end;

TG25_z := function(p, i0)
  return TG25_PermFromMapPair(p,
    function(ij)
      if ij[1] <> i0 then return ij; fi;
      return [ij[1], (ij[2]+1) mod p];
    end
  );
end;

TG25_inv := function(p, i0)
  return TG25_LiftWithin(p, TG25_WithinPerm_Inversion(p), i0);
end;

TG25_mul2 := function(p, i0)
  return TG25_LiftWithin(p, TG25_WithinPerm_Mul2(p), i0);
end;

#############################################################################
# TID utilities (known/new)
#############################################################################
TG25_TIDPair := function(G)
  local tid;
  tid := TransitiveIdentification(G);
  if IsList(tid) then return [25, tid[2]]; fi;
  return [25, tid];
end;

TG25_TIDKey := function(t)
  return Concatenation("25:", String(t[2]));
end;

TG25_KeySet := function(pairs)
  local seen, t;
  seen := rec();
  for t in pairs do
    seen.(TG25_TIDKey(t)) := true;
  od;
  return seen;
end;

TG25_UniquePairs := function(pairs)
  local seen, out, t, key;
  seen := rec(); out := [];
  for t in pairs do
    key := TG25_TIDKey(t);
    if not IsBound(seen.(key)) then
      seen.(key) := true;
      Add(out, t);
    fi;
  od;
  Sort(out, function(a,b) return a[2] < b[2]; end);
  return out;
end;

TG25_PrintPairs := function(title, pairs)
  local perLine, i;
  perLine := 12;
  if title <> "" then Print(title, "\n"); fi;
  Print("[ ");
  for i in [1..Length(pairs)] do
    Print("[25, ", pairs[i][2], "]");
    if i < Length(pairs) then Print(", "); fi;
    if i < Length(pairs) and (i mod perLine = 0) then Print("\n  "); fi;
  od;
  Print(" ]\n");
end;

#############################################################################
# Build basis rows for a given row-span (robust; no BaseMat)
#############################################################################
TG25_BaseRows := function(F, rows)
  local V, U, d;
  if rows = fail then return fail; fi;
  if not IsList(rows) or Length(rows)=0 then return []; fi;

  d := Length(rows[1]);
  V := FullRowSpace(F, d);
  U := Subspace(V, List(rows, r -> Vector(F, TG25_RowsAsPlainLists([r], d)[1])));
  return List(BasisVectors(Basis(U)), v -> List([1..d], i -> v[i]));
end;

#############################################################################
# H-invariant subspaces of permutation module F^5
#############################################################################
TG25_PermMatrix := function(F, g)
  local n, M, i, j;
  n := 5;
  M := NullMat(n, n, F);
  for i in [1..n] do
    j := i ^ g;
    M[i][j] := One(F);
  od;
  return M;
end;

TG25_SubspaceBasisRows := function(S, F)
  local rows, b;

  if S = fail then return fail; fi;

  # (A) already list of rows (list-of-lists)
  if IsList(S) and (Length(S)=0 or IsList(S[1])) then
    return S;
  fi;

  # (B) list of vectors (MTX.BasesSubmodules often gives this)
  if IsList(S) and Length(S) > 0 and not IsList(S[1]) then
    rows := [];
    for b in S do
      Add(rows, List([1..5], i -> b[i]));
    od;
    return rows;
  fi;

  # (C) vector space-like
  if IsVectorSpace(S) then
    rows := [];
    for b in BasisVectors(Basis(S)) do
      Add(rows, List([1..5], i -> b[i]));
    od;
    return rows;
  fi;

  # (D) record with .basis
  if IsRecord(S) and IsBound(S.basis) then
    rows := [];
    for b in S.basis do
      Add(rows, List([1..5], i -> b[i]));
    od;
    return rows;
  fi;

  return fail;
end;

TG25_InvariantSubspaces_MTX_or_Brute := function(H, F, useMTX)
  local mats, Mmod, bases, V, all, subs, U, ok, g, b, w, GM;

  mats := List(GeneratorsOfGroup(H), gg -> TG25_PermMatrix(F, gg));

  if useMTX then
    Mmod := fail;

    if IsBoundGlobal("GModuleByMats") then
      GM := ValueGlobal("GModuleByMats");
      if IsFunction(GM) then
        Mmod := GM(mats, F);
      fi;
    fi;

    if Mmod = fail and IsBound(MTX) and IsBound(MTX.GModuleByMats) and IsFunction(MTX.GModuleByMats) then
      Mmod := MTX.GModuleByMats(mats, F);
    fi;

    if Mmod <> fail and IsBound(MTX.BasesSubmodules) and IsFunction(MTX.BasesSubmodules) then
      bases := MTX.BasesSubmodules(Mmod);   # list of bases
      return bases;                         # caller uses TG25_SubspaceBasisRows
    fi;
  fi;

  # fallback brute
  V := FullRowSpace(F, 5);
  all := Subspaces(V);
  subs := [];

  for U in all do
    ok := true;
    for g in GeneratorsOfGroup(H) do
      for b in BasisVectors(Basis(U)) do
        w := List([1..5], i -> b[i^(g^-1)]);
        if not (Vector(F, w) in U) then ok := false; break; fi;
      od;
      if not ok then break; fi;
    od;
    if ok then Add(subs, U); fi;
  od;

  return subs;
end;

#############################################################################
# Convert basis rows -> subgroup in Sym(25)
#############################################################################
TG25_TransFromRow := function(zList, row, p)
  local g, i, c;
  g := ();
  for i in [1..5] do
    c := IntFFE(row[i]) mod p;
    if c <> 0 then g := g * (zList[i]^c); fi;
  od;
  return g;
end;

TG25_SubgroupFromRows_Cp := function(zList, rows, p)
  local gens, r;
  gens := [];
  for r in rows do
    Add(gens, TG25_TransFromRow(zList, r, p));
  od;
  if Length(gens) = 0 then return Group(()); fi;
  return Group(gens);
end;

TG25_SubgroupFromRows_C2 := function(invList, rows)
  local gens, r, g, i, bit;
  gens := [];
  for r in rows do
    g := ();
    for i in [1..5] do
      bit := IntFFE(r[i]) mod 2;
      if bit = 1 then g := g * invList[i]; fi;
    od;
    Add(gens, g);
  od;
  if Length(gens) = 0 then return Group(()); fi;
  return Group(gens);
end;

TG25_SubgroupFromRows_C4_01 := function(mul2List, rows)
  local gens, r, g, i, bit;
  gens := [];
  for r in rows do
    g := ();
    for i in [1..5] do
      bit := IntFFE(r[i]) mod 2;
      if bit = 1 then g := g * mul2List[i]; fi;
    od;
    Add(gens, g);
  od;
  if Length(gens) = 0 then return Group(()); fi;
  return Group(gens);
end;

#############################################################################
# Standard diagonal ratio subgroup C4^4 and its xC2 variant
#############################################################################
TG25_DiagRatio_C4_4 := function(mul2List)
  local gens, i;
  gens := [];
  for i in [1..4] do
    Add(gens, mul2List[i] * (mul2List[5]^-1));
  od;
  return Group(gens);
end;

TG25_DiagRatio_C4_4_xC2 := function(mul2List)
  local R;
  R := TG25_DiagRatio_C4_4(mul2List);
  return Group(Concatenation(GeneratorsOfGroup(R), [mul2List[5]^2]));
end;

#############################################################################
# Candidate generation (1)(2)(3) per H
#############################################################################
TG25_TopLift := function(H, p)
  return Group(List(GeneratorsOfGroup(H), g -> TG25_LiftBlocks(p, g)));
end;



# Nonstandard Top lifts: mix block permutation with within-block automorphisms (C4 = <mul2>)
# Returns 5 fixed variants (including plain).
TG25_LiftBlocks_WithWithin := function(p, h, withinList, where)
  local imH, img, x, i, j, ii, w, imW, jp;

  # use ListPerm to avoid relying on point^perm methods
  imH := ListPerm(h, p);   # imH[a] = a^h

  img := [];
  for x in [0..p*p-1] do
    i := x mod p;            # block index (0..p-1)
    j := QuoInt(x, p);       # within index (0..p-1)

    ii := imH[i+1] - 1;      # destination block (0..p-1)

    if where = "dest" then
      w := withinList[ii+1];
    else
      w := withinList[i+1];
    fi;

    imW := ListPerm(w, p);
    jp  := imW[j+1];         # in 1..p

    Add(img, ii + (jp-1)*p + 1);
  od;

  return PermList(img);
end;

TG25_TopLiftData := function(H, p, name, withinList, where)
  local gensH, liftGens;
  gensH := GeneratorsOfGroup(H);
  liftGens := List(gensH, g -> TG25_LiftBlocks_WithWithin(p, g, withinList, where));
  return rec(name:=name, Top:=Group(liftGens), liftGens:=liftGens);
end;

TG25_TopLiftDatas5 := function(H, p)
  local wId, w2, winv, W, where, names, out, i;
  wId  := ();
  w2   := TG25_WithinPerm_Mul2(p);       # order 4
  winv := TG25_WithinPerm_Inversion(p);  # order 2 (= w2^2)

  W := [
    List([1..5], i->wId),                 # (1) plain
    List([1..5], i->w2),                  # (2) dest uniform mul2
    List([1..5], i->winv),                # (3) dest uniform inversion
    [wId, w2, w2^2, w2^3, wId],           # (4) dest diagonal powers
    [w2, wId, w2^2, wId, w2^3]            # (5) src mixed powers
  ];

  where := ["dest","dest","dest","dest","src"];
  names := ["plain","dest_mul2","dest_inv","dest_diagPow","src_mixPow"];

  out := [];
  for i in [1..5] do
    Add(out, TG25_TopLiftData(H, p, names[i], W[i], where[i]));
  od;

  return out;
end;

TG25_Cands_1_PermModule_GF5 := function(H, useMTX, zList, Top)
  local subs, F, out, S, rows, K, G;
  F := GF(5);
  out := [];
  subs := TG25_InvariantSubspaces_MTX_or_Brute(H, F, useMTX);

  for S in subs do
    rows := TG25_SubspaceBasisRows(S, F);
    if rows = fail then continue; fi;

    K := TG25_SubgroupFromRows_Cp(zList, rows, 5);
    if Size(K) = 1 then continue; fi;

    G := Group(Concatenation(GeneratorsOfGroup(K), GeneratorsOfGroup(Top)));
    Add(out, G);
  od;

  return out;
end;

TG25_Cands_2_Twist_C2_Inv_GF2 := function(H, useMTX, zList, invList, Top)
  local subs, F, out, S, rows, E, G;
  F := GF(2);
  out := [];
  subs := TG25_InvariantSubspaces_MTX_or_Brute(H, F, useMTX);

  for S in subs do
    rows := TG25_SubspaceBasisRows(S, F);
    if rows = fail then continue; fi;

    E := TG25_SubgroupFromRows_C2(invList, rows);
    G := Group(Concatenation(zList, GeneratorsOfGroup(E), GeneratorsOfGroup(Top)));
    Add(out, G);
  od;

  return out;
end;

TG25_Cands_3_Diagonal_C4 := function(H, useMTX, zList, invList, mul2List, Top, opts)
  local out, F, subs2, S, rows, D01, D2, R, Rx2, Einv;

  out := [];
  F := GF(2);

  R   := TG25_DiagRatio_C4_4(mul2List);
  Rx2 := TG25_DiagRatio_C4_4_xC2(mul2List);

  Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R),   GeneratorsOfGroup(Top))));
  Add(out, Group(Concatenation(zList, GeneratorsOfGroup(Rx2), GeneratorsOfGroup(Top))));

  subs2 := TG25_InvariantSubspaces_MTX_or_Brute(H, F, useMTX);

  for S in subs2 do
    rows := TG25_SubspaceBasisRows(S, F);
    if rows = fail then continue; fi;

    D01 := TG25_SubgroupFromRows_C4_01(mul2List, rows);
    D2  := Group(List(GeneratorsOfGroup(D01), g -> g^2));

    Add(out, Group(Concatenation(zList, GeneratorsOfGroup(D01), GeneratorsOfGroup(Top))));
    Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R),   GeneratorsOfGroup(D2),  GeneratorsOfGroup(Top))));
    Add(out, Group(Concatenation(zList, GeneratorsOfGroup(Rx2), GeneratorsOfGroup(D2),  GeneratorsOfGroup(Top))));

    if IsBound(opts.doDiagWithInv) and opts.doDiagWithInv = true then
      Einv := TG25_SubgroupFromRows_C2(invList, rows);
      Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R), GeneratorsOfGroup(D2),
                                   GeneratorsOfGroup(Einv), GeneratorsOfGroup(Top))));
    fi;
  od;

  return out;
end;

#############################################################################
# (4) Twist layer on quotient W = GF(5)^5 / U  (Schreier constraints)
#############################################################################
TG25_ActRowPerm5 := function(v, g)
  return List([1..5], i -> v[i^(g^-1)]);
end;

TG25_QuotData_GF5_FromRows := function(rowsU)
  local F, basisU, dimU, comp, B, invB, i, e, rank0, rank1;

  F := GF(5);
  if rowsU = fail then return fail; fi;

  basisU := TG25_BaseRows(F, rowsU);
  if basisU = fail then return fail; fi;
  dimU := Length(basisU);

  comp := [];
  rank0 := TG25_RankRows(F, Concatenation(basisU, comp), 5);

  for i in [1..5] do
    e := TG25_StdBasisVec(F, 5, i);
    rank1 := TG25_RankRows(F, Concatenation(basisU, comp, [e]), 5);
    if rank1 > rank0 then
      Add(comp, e);
      rank0 := rank1;
    fi;
  od;

  if dimU + Length(comp) <> 5 then
    return fail;
  fi;

  B := Concatenation(basisU, comp);                 # 5 rows
  invB := Inverse(Matrix(F, TG25_RowsAsPlainLists(B, 5)));

  return rec(F:=F, basisU:=basisU, dimU:=dimU,
             compBasis:=comp, d:=Length(comp),
             Bfull:=B, invB:=invB);
end;

TG25_QuotProj := function(qd, v)
  local c, L;
  c := Vector(qd.F, v) * qd.invB;
  L := List([1..5], i -> c[i]);
  return L{[qd.dimU+1 .. 5]};
end;

TG25_QuotLift := function(qd, q)
  local v, i, j;
  v := List([1..5], t -> Zero(qd.F));
  for j in [1..qd.d] do
    for i in [1..5] do
      v[i] := v[i] + q[j] * qd.compBasis[j][i];
    od;
  od;
  return v;
end;

TG25_ActionMatOnQuot := function(qd, g)
  local d, F, M, j, q, v, vp, qp;
  d := qd.d; F := qd.F;
  M := NullMat(d, d, F);

  for j in [1..d] do
    q := List([1..d], t -> Zero(F)); q[j] := One(F);
    v := TG25_QuotLift(qd, q);
    vp := TG25_ActRowPerm5(v, g);
    qp := TG25_QuotProj(qd, vp);
    M[j] := qp;
  od;

  return M;
end;

TG25_SelBlock := function(F, r, d, i)
  local n, S, j;
  n := r*d;
  S := NullMat(n, d, F);
  for j in [1..d] do
    S[(i-1)*d + j][j] := One(F);
  od;
  return S;
end;

TG25_CoeffTuples_Limited := function(F, k, maxOut, skipZero)
  local q, els, out, t, coeffs, tmp, i, digit, allZero;
  q := Size(F);
  els := Elements(F);
  out := [];
  t := 0;

  while Length(out) < maxOut do
    coeffs := [];
    tmp := t;
    allZero := true;

    for i in [1..k] do
      digit := tmp mod q;
      tmp := QuoInt(tmp, q);
      coeffs[i] := els[digit+1];
      if coeffs[i] <> Zero(F) then allZero := false; fi;
    od;

    if not (skipZero and allZero) then
      Add(out, coeffs);
    fi;

    t := t + 1;
  od;

  return out;
end;

TG25_CoeffTuples_Random := function(F, k, maxOut, skipZero)
  local els, out, coeffs, i, allZero;
  els := Elements(F);
  out := [];

  while Length(out) < maxOut do
    coeffs := [];
    allZero := true;

    for i in [1..k] do
      coeffs[i] := Random(els);
      if coeffs[i] <> Zero(F) then allZero := false; fi;
    od;

    if skipZero and allZero then
      continue;
    fi;

    # maxOut is small in our usage, so linear membership check is fine
    if not coeffs in out then
      Add(out, coeffs);
    fi;
  od;

  return out;
end;

# mode = "lex" or "random"
TG25_CoeffTuples := function(F, k, maxOut, skipZero, mode)
  if mode = "random" then
    return TG25_CoeffTuples_Random(F, k, maxOut, skipZero);
  fi;
  return TG25_CoeffTuples_Limited(F, k, maxOut, skipZero);
end;


TG25_H1Reps_Quot_Schreier := function(H, qd, opts)
  local F, gens, r, d, n, maxReps, skipZero,
        elts, m, id, idIdx, visited, Q, head, parentIdx, g, i,
        Mgen, Sel, M, C, EqM, child, childIdx, Calt, D, j, row,
        Zbasis, Bgens, a, aVec, act, xi, Sspan, Qbasis, rankBefore, rankAfter,
        reps, coeffTuples, coeffs, v, t, ii, mode;

  F := qd.F;
  d := qd.d;
  if d = 0 then return []; fi;

  maxReps := 200;
  if IsBound(opts.twistMaxReps) then maxReps := opts.twistMaxReps; fi;

  skipZero := true;
  if IsBound(opts.twistSkipZero) then skipZero := opts.twistSkipZero; fi;

  gens := GeneratorsOfGroup(H);
  r := Length(gens);
  n := r*d;

  Mgen := List([1..r], k -> TG25_ActionMatOnQuot(qd, gens[k]));
  Sel  := List([1..r], k -> TG25_SelBlock(F, r, d, k));

  elts := Elements(H);
  m := Length(elts);
  id := One(H);
  idIdx := Position(elts, id);

  visited := List([1..m], k -> false);
  Q := [];
  head := 1;

  M := List([1..m], k -> fail);
  C := List([1..m], k -> fail);
  EqM := [];

  visited[idIdx] := true;
  Add(Q, idIdx);
  M[idIdx] := IdentityMat(d, F);
  C[idIdx] := NullMat(n, d, F);

  while head <= Length(Q) do
    parentIdx := Q[head]; head := head + 1;
    g := elts[parentIdx];

    for i in [1..r] do
      child := g * gens[i];
      childIdx := Position(elts, child);

      Calt := C[parentIdx] + Sel[i] * M[parentIdx];

      if not visited[childIdx] then
        visited[childIdx] := true;
        Add(Q, childIdx);
        M[childIdx] := M[parentIdx] * Mgen[i];
        C[childIdx] := Calt;
      else
        D := C[childIdx] - Calt;     # (n x d)
        for j in [1..d] do
          row := List([1..n], k -> D[k][j]);
          Add(EqM, row);
        od;
      fi;
    od;
  od;

  # Z^1 = nullspace(EqM)
  if Length(EqM) = 0 then
    Zbasis := List([1..n], function(t)
      return List([1..n], function(ii)
        if ii = t then return One(F); else return Zero(F); fi;
      end);
    end);
  else
    Zbasis := TG25_NullspaceRows(F, EqM, n);
  fi;

  # B^1 generators
  Bgens := [];
  for j in [1..d] do
    a := List([1..d], t -> Zero(F)); a[j] := One(F);
    aVec := Vector(F, a);

    xi := [];
    for i in [1..r] do
      act := aVec * Mgen[i];  # row action
      Append(xi, List([1..d], t -> a[t] - act[t]));
    od;
    Add(Bgens, xi);
  od;

  Sspan := [];
  if Length(Bgens) > 0 then
    Sspan := TG25_BaseRows(F, Bgens);
  fi;

  Qbasis := [];
  for v in Zbasis do
    rankBefore := TG25_RankRows(F, Sspan, n);
    rankAfter  := TG25_RankRows(F, Concatenation(Sspan, [v]), n);
    if rankAfter > rankBefore then
      Add(Sspan, v);
      Add(Qbasis, v);
    fi;
  od;

  if Length(Qbasis) = 0 then return []; fi;

  reps := [];
  mode := "lex";
  if IsBound(opts.twistMode) then mode := opts.twistMode; fi;

  coeffTuples := TG25_CoeffTuples(F, Length(Qbasis), maxReps, skipZero, mode);
for coeffs in coeffTuples do
    v := List([1..n], t -> Zero(F));
    for ii in [1..Length(Qbasis)] do
      if coeffs[ii] <> Zero(F) then
        for t in [1..n] do
          v[t] := v[t] + coeffs[ii] * Qbasis[ii][t];
        od;
      fi;
    od;
    Add(reps, v);
  od;

  return reps;
end;

TG25_Cands_4_TwistOnQuot_GF5 := function(H, useMTX, zList, liftGens, opts)
  local F, subs, out, S, rowsU, qd, repsX, r, d,
        K, X, twisted, i, xi, vi, ki, gi, G;

  F := GF(5);
  subs := TG25_InvariantSubspaces_MTX_or_Brute(H, F, useMTX);

  out := [];
  r := Length(liftGens);
for S in subs do
    rowsU := TG25_SubspaceBasisRows(S, F);
    if rowsU = fail then continue; fi;

    qd := TG25_QuotData_GF5_FromRows(rowsU);
    if qd = fail or qd.d = 0 then continue; fi;

    d := qd.d;
    K := TG25_SubgroupFromRows_Cp(zList, rowsU, 5);

    repsX := TG25_H1Reps_Quot_Schreier(H, qd, opts);
    if Length(repsX) = 0 then continue; fi;

    for X in repsX do
      twisted := [];
      for i in [1..r] do
        xi := X{[(i-1)*d+1 .. i*d]};
        vi := TG25_QuotLift(qd, xi);
        ki := TG25_TransFromRow(zList, vi, 5);
        gi := ki * liftGens[i];
        Add(twisted, gi);
      od;

      G := Group(Concatenation(GeneratorsOfGroup(K), twisted));
      Add(out, G);
    od;
  od;

  return out;
end;

#############################################################################
# One-pass runner with known/new report (1)(2)(3)(4)
#############################################################################
TG25_Run_Fill1234_MTX := function(opts)
  local p, useMTX, TopDatas, td, do4All,
        knownTIDs, knownPairs, knownSet,
        do1, do2, do3, do4,
        t, targetsSet, wantOnly,
        zList, invList, mul2List,
        Hs, Hid, H, Top,
        all, foundPairs, G, key, oldPairs, newPairs;

  p := 5;
  useMTX := true;

  knownTIDs := [];
  if IsBound(opts.knownTIDs) then knownTIDs := opts.knownTIDs; fi;

  knownPairs := List(knownTIDs, function(x)
    if IsList(x) then return [25, x[2]]; else return [25, x]; fi;
  end);

  knownSet := TG25_KeySet(knownPairs);

  do1 := true; do2 := true; do3 := true; do4 := true;
  if IsBound(opts.do1) then do1 := opts.do1; fi;
  if IsBound(opts.do2) then do2 := opts.do2; fi;
  if IsBound(opts.do3) then do3 := opts.do3; fi;
  if IsBound(opts.do4) then do4 := opts.do4; fi;

  if not IsBound(opts.doDiagWithInv) then opts.doDiagWithInv := false; fi;
  if not IsBound(opts.twistMaxReps) then opts.twistMaxReps := 5; fi;
  if not IsBound(opts.twistSkipZero) then opts.twistSkipZero := true; fi;

  wantOnly := false;
  targetsSet := rec();
  if IsBound(opts.targets) then
    wantOnly := true;
    for t in opts.targets do
      targetsSet.(Concatenation("25:", String(t[2]))) := true;
    od;
  fi;

  zList    := List([0..4], i0 -> TG25_z(p, i0));
  invList  := List([0..4], i0 -> TG25_inv(p, i0));
  mul2List := List([0..4], i0 -> TG25_mul2(p, i0));

  Hs := List([1..NrTransitiveGroups(5)], k -> TransitiveGroup(5,k));

  all := [];
  for Hid in [1..Length(Hs)] do
    
H := Hs[Hid];

# 5 lift variants (including plain)

TopDatas := TG25_TopLiftDatas5(H, p);

do4All := false;
if IsBound(opts.do4AllLifts) then do4All := opts.do4AllLifts; fi;

for td in TopDatas do
  Top := td.Top;

      if do1 then Append(all, TG25_Cands_1_PermModule_GF5(H, useMTX, zList, Top)); fi;
    if do2 then Append(all, TG25_Cands_2_Twist_C2_Inv_GF2(H, useMTX, zList, invList, Top)); fi;
    if do3 then Append(all, TG25_Cands_3_Diagonal_C4(H, useMTX, zList, invList, mul2List, Top, opts)); fi;
    if do4 and (do4All or td.name = "plain") then
        Append(all, TG25_Cands_4_TwistOnQuot_GF5(H, useMTX, zList, td.liftGens, opts));
      fi;
    od;

  od;

  foundPairs := [];
  for G in all do
    if IsTransitive(G, [1..25]) then
      t := TG25_TIDPair(G);
      key := TG25_TIDKey(t);

      if wantOnly and not IsBound(targetsSet.(key)) then
        continue;
      fi;

      Add(foundPairs, t);
    fi;
  od;

  foundPairs := TG25_UniquePairs(foundPairs);

  oldPairs := []; newPairs := [];
  for t in foundPairs do
    key := TG25_TIDKey(t);
    if IsBound(knownSet.(key)) then Add(oldPairs, t); else Add(newPairs, t); fi;
  od;

  Print("\n=== summary: unique TIDs found (this scan) ===\n");
  TG25_PrintPairs("", foundPairs);

  Print("\n=== existing TIDs (already known) ===\n");
  TG25_PrintPairs("", oldPairs);

  Print("\n=== new TIDs (not in known list) ===\n");
  TG25_PrintPairs("", newPairs);

  return rec(allTIDs:=foundPairs, old:=oldPairs, new:=newPairs);
end;

#############################################################################
# Optional autorun
#############################################################################
if not IsBound(TG25_NO_AUTORUN) or TG25_NO_AUTORUN <> true then
  rep := TG25_Run_Fill1234_MTX(rec(
    knownTIDs := [],
    do1 := true, do2 := true, do3 := true, do4 := true,
    doDiagWithInv := true,
    twistMaxReps := 300,
    twistSkipZero := true
  ));
fi;

#############################################################################
# End of file
#############################################################################

#############################################################################
# EXTRA: 32 (max) H^1 twists in inversion/(-1)-layer + explicit K-type kernels
#   Run:
#     Read("saigo_ktypes_h1_32.g");;
#     TG25_Run_Lift32_KTypes();
#############################################################################

TG25_InvAugGens := function(invList)
  return List([1..4], i -> invList[i] * invList[5]);
end;

TG25_MulAugGens := function(mul2List)
  return List([1..4], i -> mul2List[i] * (mul2List[5]^-1));
end;

TG25_KernelVariants := function(zList, invList, mul2List)
  local out, invAug, mulAug, R, Rx2;
  out := [];
  invAug := TG25_InvAugGens(invList);
  mulAug := TG25_MulAugGens(mul2List);
  R   := TG25_DiagRatio_C4_4(mul2List);
  Rx2 := TG25_DiagRatio_C4_4_xC2(mul2List);

  # invMode:
  #   "none"   : no H^1 twisting in C2^5
  #   "inv"    : twist by inv_i (needs invList)
  #   "mul2sq" : twist by mul2_i^2 (works if kernel has C4-layer)
  Add(out, rec(name:="K_C5^5", gens:=ShallowCopy(zList), invMode:="none"));
  Add(out, rec(name:="K_C5^5_C2^5", gens:=Concatenation(zList, invList), invMode:="inv"));
  Add(out, rec(name:="K_C5^5_C2^4", gens:=Concatenation(zList, invAug), invMode:="inv"));
  Add(out, rec(name:="K_C5^5_C4^5", gens:=Concatenation(zList, mul2List), invMode:="mul2sq"));
  Add(out, rec(name:="K_C5^5_C4^4", gens:=Concatenation(zList, mulAug), invMode:="mul2sq"));
  Add(out, rec(name:="K_C5^5_ratioC4^4", gens:=Concatenation(zList, GeneratorsOfGroup(R)), invMode:="mul2sq"));
  Add(out, rec(name:="K_C5^5_ratioC4^4xC2", gens:=Concatenation(zList, GeneratorsOfGroup(Rx2)), invMode:="mul2sq"));

  return out;
end;

TG25_ElemFromVec_Inv := function(invList, v)
  local i, e, F;
  F := GF(2);
  e := ();
  for i in [1..Length(invList)] do
    if v[i] <> Zero(F) then
      e := e * invList[i];
    fi;
  od;
  return e;
end;

TG25_ElemFromVec_Mul2Sq := function(mul2List, v)
  local i, e, F;
  F := GF(2);
  e := ();
  for i in [1..Length(mul2List)] do
    if v[i] <> Zero(F) then
      e := e * (mul2List[i]^2);
    fi;
  od;
  return e;
end;

TG25_ActionMats_PermModule := function(H, F)
  local gens, mats, g;
  gens := GeneratorsOfGroup(H);
  mats := [];
  for g in gens do
    Add(mats, TG25_PermMatrix(F, g));   # 5x5
  od;
  return mats;
end;

# Generic Schreier-style computation of H^1(H, F^d) for a given generator action Mgen
TG25_H1Reps_Module_Schreier := function(H, F, Mgen, opts)
  local gens, r, d, n, maxReps, skipZero, mode,
        elts, m, id, idIdx, visited, Q, head, parentIdx, g, i,
        Sel, M, C, EqM, child, childIdx, Calt, D, j, row,
        Zbasis, Bgens, a, aVec, act, xi, Sspan, Qbasis, rankBefore, rankAfter,
        reps, coeffTuples, coeffs, v, t, ii;

  d := Length(Mgen[1]);
  if d = 0 then return []; fi;

  maxReps := 32;
  if IsBound(opts.twistMaxReps) then maxReps := opts.twistMaxReps; fi;

  skipZero := true;
  if IsBound(opts.twistSkipZero) then skipZero := opts.twistSkipZero; fi;

  mode := "lex";
  if IsBound(opts.twistMode) then mode := opts.twistMode; fi;

  gens := GeneratorsOfGroup(H);
  r := Length(gens);
  n := r*d;

  Sel := List([1..r], k -> TG25_SelBlock(F, r, d, k));

  elts := Elements(H);
  m := Length(elts);
  id := One(H);
  idIdx := Position(elts, id);

  visited := List([1..m], k -> false);
  Q := [];
  head := 1;

  M := List([1..m], k -> fail);
  C := List([1..m], k -> fail);
  EqM := [];

  visited[idIdx] := true;
  Add(Q, idIdx);
  M[idIdx] := IdentityMat(d, F);
  C[idIdx] := NullMat(n, d, F);

  while head <= Length(Q) do
    parentIdx := Q[head]; head := head + 1;
    g := elts[parentIdx];

    for i in [1..r] do
      child := g * gens[i];
      childIdx := Position(elts, child);

      Calt := C[parentIdx] + Sel[i] * M[parentIdx];

      if not visited[childIdx] then
        visited[childIdx] := true;
        Add(Q, childIdx);
        M[childIdx] := M[parentIdx] * Mgen[i];
        C[childIdx] := Calt;
      else
        D := C[childIdx] - Calt;     # (n x d)
        for j in [1..d] do
          row := List([1..n], k -> D[k][j]);
          Add(EqM, row);
        od;
      fi;
    od;
  od;

  # Z^1 = nullspace(EqM)
  if Length(EqM) = 0 then
    Zbasis := List([1..n], function(t)
      return List([1..n], function(ii)
        if ii = t then return One(F); else return Zero(F); fi;
      end);
    end);
  else
    Zbasis := TG25_NullspaceRows(F, EqM, n);
  fi;

  # B^1 generators
  Bgens := [];
  for j in [1..d] do
    a := List([1..d], t -> Zero(F)); a[j] := One(F);
    aVec := Vector(F, a);

    xi := [];
    for i in [1..r] do
      act := aVec * Mgen[i];
      Append(xi, List([1..d], t -> a[t] - act[t]));
    od;
    Add(Bgens, xi);
  od;

  Sspan := [];
  if Length(Bgens) > 0 then
    Sspan := TG25_BaseRows(F, Bgens);
  fi;

  # pick Qbasis as a complement basis of Z^1 / B^1
  Qbasis := [];
  for v in Zbasis do
    rankBefore := TG25_RankRows(F, Sspan, n);
    rankAfter  := TG25_RankRows(F, Concatenation(Sspan, [v]), n);
    if rankAfter > rankBefore then
      Add(Qbasis, v);
      Add(Sspan, v);
    fi;
  od;

  reps := [];
  if Length(Qbasis) = 0 then
    if not skipZero then Add(reps, List([1..n], t -> Zero(F))); fi;
    return reps;
  fi;

  coeffTuples := TG25_CoeffTuples(F, Length(Qbasis), maxReps, skipZero, mode);

  for coeffs in coeffTuples do
    v := List([1..n], t -> Zero(F));
    for i in [1..Length(Qbasis)] do
      if coeffs[i] <> Zero(F) then
        for t in [1..n] do
          v[t] := v[t] + coeffs[i] * Qbasis[i][t];
        od;
      fi;
    od;
    Add(reps, v);
  od;

  return reps;
end;

# Convert H^1 reps (stacked r blocks of length 5) into twisted lift generator lists
TG25_TwistLiftGens_FromH1 := function(H, liftGens, invMode, invList, mul2List, repsX)
  local gensH, r, d, out, x, i, v, ki, gi;
  gensH := GeneratorsOfGroup(H);
  r := Length(gensH);
  d := 5;

  out := [];

  for x in repsX do
    gi := [];
    for i in [1..r] do
      v := x{[(i-1)*d+1 .. i*d]};
      if invMode = "inv" then
        ki := TG25_ElemFromVec_Inv(invList, v);
      elif invMode = "mul2sq" then
        ki := TG25_ElemFromVec_Mul2Sq(mul2List, v);
      else
        ki := ();
      fi;
      Add(gi, ki * liftGens[i]);
    od;
    Add(out, gi);
  od;

  return out;
end;

# One-shot runner: K-type kernels + 5 top-lifts + (up to) 32 H^1 twists in C2^5
TG25_Run_Lift32_KTypes := function()
  local p, zList, invList, mul2List, Kvars,
        Hid, H, TopDatas, td, all, seen, key,
        F, Mgen, repsX, twisted, gensTw, kv, G, tid, opts;

  p := 5;
  zList    := List([0..4], i -> TG25_z(p, i));
  invList  := List([0..4], i -> TG25_inv(p, i));
  mul2List := List([0..4], i -> TG25_mul2(p, i));

  Kvars := TG25_KernelVariants(zList, invList, mul2List);

  all := [];
  seen := rec();

  opts := rec(twistMaxReps:=32, twistSkipZero:=true, twistMode:="lex");

  for Hid in [1..NrTransitiveGroups(5)] do
    H := TransitiveGroup(5, Hid);
    Print("\n=== H=TransitiveGroup(5,", Hid, ") |H|=", Size(H), " ===\n");

    TopDatas := TG25_TopLiftDatas5(H, p);

    # add plain/nonstandard top with each K-type (no H^1 twist)
    for td in TopDatas do
      for kv in Kvars do
        G := Group(Concatenation(kv.gens, GeneratorsOfGroup(td.Top)));
        tid := TG25_TIDPair(G);
        key := TG25_TIDKey(tid);
        if not IsBound(seen.(key)) then
          seen.(key) := true;
          Add(all, tid);
        fi;
      od;
    od;

    # H^1 twists for module GF(2)^5 (block-permutation action)
    F := GF(2);
    Mgen := TG25_ActionMats_PermModule(H, F);
    repsX := TG25_H1Reps_Module_Schreier(H, F, Mgen, opts);

    # base lift gens for gens(H): use "plain" lift data (TopDatas[1])
    td := TopDatas[1];

    for kv in Kvars do
      if kv.invMode = "none" then
        continue;
      fi;

      twisted := TG25_TwistLiftGens_FromH1(H, td.liftGens, kv.invMode, invList, mul2List, repsX);

      for gensTw in twisted do
        G := Group(Concatenation(kv.gens, gensTw));
        tid := TG25_TIDPair(G);
        key := TG25_TIDKey(tid);
        if not IsBound(seen.(key)) then
          seen.(key) := true;
          Add(all, tid);
        fi;
      od;
    od;
  od;

  all := TG25_UniquePairs(all);
  Print("\n=== summary: unique TIDs found (K-types + 5 lifts + H^1 up to 32) ===\n");
  TG25_PrintPairs("", all);
  return all;
end;

#############################################################################
# EXTRA2: enumerate all H-invariant subspaces U <= GF(2)^5 (perm module)
# and build kernels K = <C5^5, Inv(U)> and K = <C5^5, Mul2(U)>,
# plus H^1(H,U) twists (up to 32) for the inversion layer.
#
# Run:
#   Read("saigo_invsubspaces32_fixed.g");;
#   TG25_Run_InvSubspaces32();
#############################################################################

# bitwise XOR on 5-bit masks (0..31), implemented arithmetically (no bit operators)
TG25_XorInt5 := function(a, b)
  local res, i, abit, bbit;
  res := 0;
  for i in [0..4] do
    abit := QuoInt(a, 2^i) mod 2;
    bbit := QuoInt(b, 2^i) mod 2;
    if (abit + bbit) mod 2 = 1 then
      res := res + 2^i;
    fi;
  od;
  return res;
end;

# apply permutation im (list length 5, values 1..5) to mask m (0..31)
TG25_MaskApplyPerm := function(im, m)
  local res, i;
  res := 0;
  for i in [1..5] do
    if (QuoInt(m, 2^(i-1)) mod 2) = 1 then
      res := res + 2^(im[i]-1);
    fi;
  od;
  return res;
end;

TG25_SpanBoolFromBasisMasks := function(basisMasks)
  local d, span, c, j, v;
  d := Length(basisMasks);
  span := List([1..32], i -> false);   # index = mask+1
  for c in [0..(2^d)-1] do
    v := 0;
    for j in [1..d] do
      if (QuoInt(c, 2^(j-1)) mod 2) = 1 then
        v := TG25_XorInt5(v, basisMasks[j]);
      fi;
    od;
    span[v+1] := true;
  od;
  return span;
end;

# enumerate all row-reduced bases (as bitmasks) for d-dim subspaces of GF(2)^5
TG25_RREFBases_GF2_5 := function(d)
  local pivs, choosePivs, P, free, allow, totalBits, all, bitpos, assign,
        rows, r, row, k, cols, acc, c;

  all := [];

  choosePivs := function(start, left, acc)
    if left = 0 then
      Add(pivs, ShallowCopy(acc));
      return;
    fi;
    for c in [start..(5-left+1)] do
      Add(acc, c);
      choosePivs(c+1, left-1, acc);
      Unbind(acc[Length(acc)]);
    od;
  end;

  pivs := [];
  choosePivs(1, d, []);

  for P in pivs do
    free := Filtered([1..5], x -> not x in P);

    allow := [];
    totalBits := 0;
    for r in [1..d] do
      cols := Filtered(free, c -> c > P[r]);
      allow[r] := cols;
      totalBits := totalBits + Length(cols);
    od;

    for assign in [0..(2^totalBits)-1] do
      rows := [];
      bitpos := 0;
      for r in [1..d] do
        row := 2^(P[r]-1);
        cols := allow[r];
        for k in [1..Length(cols)] do
          if (QuoInt(assign, 2^bitpos) mod 2) = 1 then
            row := row + 2^(cols[k]-1);
          fi;
          bitpos := bitpos + 1;
        od;
        Add(rows, row);
      od;
      Add(all, rows);
    od;
  od;

  return all;
end;

# list all H-invariant subspaces of dims in 'dims', inside GF(2)^5 perm module
TG25_InvariantSubspaces_GF2_5 := function(H, dims)
  local gensH, ims, d, bases, B, span, ok, im, v, out;

  gensH := GeneratorsOfGroup(H);
  ims := List(gensH, g -> ListPerm(g, 5));  # im[i]=i^g

  out := [];

  for d in dims do
    bases := TG25_RREFBases_GF2_5(d);
    for B in bases do
      span := TG25_SpanBoolFromBasisMasks(B);
      ok := true;
      for im in ims do
        for v in [0..31] do
          if span[v+1] then
            if not span[TG25_MaskApplyPerm(im, v)+1] then
              ok := false; break;
            fi;
          fi;
        od;
        if not ok then break; fi;
      od;

      if ok then
        Add(out, rec(dim:=d, basisMasks:=B, spanBool:=span));
      fi;
    od;
  od;

  return out;
end;

TG25_ElemFromMaskBasis := function(elemList, mask)
  local e, i;
  e := ();
  for i in [1..5] do
    if (QuoInt(mask, 2^(i-1)) mod 2) = 1 then
      e := e * elemList[i];
    fi;
  od;
  return e;
end;

# induced action matrices on U (basis coordinate action), returned as list of dxd matrices (rows)
TG25_InducedActionMats_OnSubspace := function(H, U)
  local F, d, gensH, ims, mapCoeff, c, j, v, coeffVec, B, Mgen, im, i, imgMask, row;

  F := GF(2);
  d := U.dim;

  gensH := GeneratorsOfGroup(H);
  ims := List(gensH, g -> ListPerm(g, 5));

  mapCoeff := [];
  for v in [0..31] do mapCoeff[v+1] := fail; od;

  for c in [0..(2^d)-1] do
    v := 0;
    coeffVec := List([1..d], t -> Zero(F));
    for j in [1..d] do
      if (QuoInt(c, 2^(j-1)) mod 2) = 1 then
        v := TG25_XorInt5(v, U.basisMasks[j]);
        coeffVec[j] := One(F);
      fi;
    od;
    mapCoeff[v+1] := coeffVec;
  od;

  Mgen := [];
  for im in ims do
    B := [];
    for i in [1..d] do
      imgMask := TG25_MaskApplyPerm(im, U.basisMasks[i]);
      row := mapCoeff[imgMask+1];
      if row = fail then Error("induced action: image not in span (bug)"); fi;
      Add(B, row);
    od;
    Add(Mgen, B);  # dxd over GF(2), rows
  od;

  return Mgen;
end;

TG25_TwistLiftGens_FromH1_Coords := function(H, liftGens, basisElems, repsX)
  local gensH, r, d, out, x, i, v, gi, j, e, F;

  gensH := GeneratorsOfGroup(H);
  r := Length(gensH);
  d := Length(basisElems);
  F := GF(2);

  out := [];

  for x in repsX do
    gi := [];
    for i in [1..r] do
      v := x{[(i-1)*d+1 .. i*d]};
      e := ();
      for j in [1..d] do
        if v[j] <> Zero(F) then
          e := e * basisElems[j];
        fi;
      od;
      Add(gi, e * liftGens[i]);
    od;
    Add(out, gi);
  od;

  return out;
end;

TG25_Run_InvSubspaces32 := function()
  local p, zList, invList, mul2List,
        Hid, H, TopDatas, td,
        Ulist, U, basisElemsInv, basisElemsMul2,
        K, G, tid, key, seen, all,
        F, Mgen, repsX, opts, twisted, gensTw;

  p := 5;
  zList    := List([0..4], i -> TG25_z(p, i));
  invList  := List([0..4], i -> TG25_inv(p, i));
  mul2List := List([0..4], i -> TG25_mul2(p, i));

  seen := rec();
  all := [];

  opts := rec(twistMaxReps:=32, twistSkipZero:=true, twistMode:="lex");

  for Hid in [1..NrTransitiveGroups(5)] do
    H := TransitiveGroup(5, Hid);
    Print("\n=== H=TransitiveGroup(5,", Hid, ") |H|=", Size(H), " ===\n");

    TopDatas := TG25_TopLiftDatas5(H, p);

    # dims 4,5 are the ones that matter for C2^4 / C2^5
    Ulist := TG25_InvariantSubspaces_GF2_5(H, [4,5]);
    Print("  invariant subspaces dims 4/5: ", Length(Ulist), "\n");

    for U in Ulist do
      # build Inv(U)
      basisElemsInv := List(U.basisMasks, m -> TG25_ElemFromMaskBasis(invList, m));
      K := Group(Concatenation(zList, basisElemsInv));

      for td in TopDatas do
        G := Group(Concatenation(GeneratorsOfGroup(K), GeneratorsOfGroup(td.Top)));
        tid := TG25_TIDPair(G);
        key := TG25_TIDKey(tid);
        if not IsBound(seen.(key)) then
          seen.(key) := true;
          Add(all, tid);
        fi;
      od;

      # H^1(H,U) twists (plain top only)
      F := GF(2);
      Mgen := TG25_InducedActionMats_OnSubspace(H, U);
      repsX := TG25_H1Reps_Module_Schreier(H, F, Mgen, opts);

      td := TopDatas[1];  # plain
      twisted := TG25_TwistLiftGens_FromH1_Coords(H, td.liftGens, basisElemsInv, repsX);

      for gensTw in twisted do
        G := Group(Concatenation(GeneratorsOfGroup(K), gensTw));
        tid := TG25_TIDPair(G);
        key := TG25_TIDKey(tid);
        if not IsBound(seen.(key)) then
          seen.(key) := true;
          Add(all, tid);
        fi;
      od;

      # also: build Mul2(U) inside C4^5 (no H^1 twist here)
      basisElemsMul2 := List(U.basisMasks, m -> TG25_ElemFromMaskBasis(mul2List, m));
      K := Group(Concatenation(zList, basisElemsMul2));
      for td in TopDatas do
        G := Group(Concatenation(GeneratorsOfGroup(K), GeneratorsOfGroup(td.Top)));
        tid := TG25_TIDPair(G);
        key := TG25_TIDKey(tid);
        if not IsBound(seen.(key)) then
          seen.(key) := true;
          Add(all, tid);
        fi;
      od;
    od;
  od;

  all := TG25_UniquePairs(all);
  Print("\n=== summary: unique TIDs found (inv subspaces dims 4/5 + H^1 up to 32 + mul2 subspaces) ===\n");
  TG25_PrintPairs("", all);
  return all;
end;

#############################################################################
# Z/4 addon: H^1(H, (Z/4)^5) twists for the C4-layer (mul2), up to 32 reps.
#
# Prereq:
#   TG25_NO_AUTORUN := true;;
#   Read("saigo_invsubspaces32_fixed.g");;
#
# Use:
#   Read("z4_addon.g");;
#   TG25_Run_Z4_Twists32();;
#############################################################################

TG25_Mod4 := function(x)
  x := x mod 4;
  if x < 0 then x := x + 4; fi;
  return x;
end;

TG25_AddMod4 := function(a,b) return TG25_Mod4(a+b); end;
TG25_SubMod4 := function(a,b) return TG25_Mod4(a-b); end;
TG25_MulMod4 := function(a,b) return TG25_Mod4(a*b); end;

# row-vector v * matrix M over Z/4
TG25_RowTimesMat_Mod4 := function(v, M)
  local d, w, j, t, s;
  d := Length(v);
  w := List([1..d], j -> 0);
  for j in [1..d] do
    s := 0;
    for t in [1..d] do
      s := TG25_AddMod4(s, TG25_MulMod4(v[t], M[t][j]));
    od;
    w[j] := s;
  od;
  return w;
end;

# 5x5 permutation matrix over Z/4 (entries 0/1)
TG25_PermMatrixMod4 := function(g)
  local im, M, i;
  im := ListPerm(g, 5);  # im[i]=i^g
  M := List([1..5], i -> List([1..5], j -> 0));
  for i in [1..5] do
    M[i][im[i]] := 1;
  od;
  return M;
end;

# (C4)^n element <-> exponent vector length n
TG25_AElemFromVec4 := function(A, vec)
  local gens, e, i;
  gens := Pcgs(A);
  e := One(A);
  for i in [1..Length(vec)] do
    if vec[i] <> 0 then
      e := e * gens[i]^vec[i];
    fi;
  od;
  return e;
end;

TG25_AVecFromElem4 := function(A, e)
  return ExponentsOfPcElement(Pcgs(A), e);
end;

# Hom(A)->B from Aeq (m x n) over Z/4, kernel = solutions of Aeq*x=0 mod4
TG25_ChooseAbelianGens := function(G, expected)
  local gens;

  gens := fail;

  if IsBoundGlobal("IndependentGeneratorsOfAbelianGroup") then
    if HasIsAbelian(G) and IsAbelian(G) then
      gens := IndependentGeneratorsOfAbelianGroup(G);
    fi;
  fi;

  if gens = fail or not IsList(gens) then
    gens := GeneratorsOfGroup(G);
  fi;

  if Length(gens) <> expected then
    # try pcgs as last resort
    if IsBoundGlobal("Pcgs") then
      gens := Pcgs(G);
    fi;
  fi;

  if Length(gens) <> expected then
    Error("TG25_ChooseAbelianGens: expected ", expected,
          " generators but got ", Length(gens));
  fi;

  return gens;
end;

TG25_HomFromMat_Mod4 := function(Aeq)
  local m, n, i, j, A, B, gensA, gensB, images, img;

  m := Length(Aeq);
  if m = 0 then
    Error("TG25_HomFromMat_Mod4: Aeq has 0 rows");
  fi;

  n := Length(Aeq[1]);
  for i in [1..m] do
    if Length(Aeq[i]) <> n then
      Error("TG25_HomFromMat_Mod4: non-rectangular matrix");
    fi;
  od;

  A := AbelianGroup(List([1..n], i -> 4));
  B := AbelianGroup(List([1..m], i -> 4));

  gensA := TG25_ChooseAbelianGens(A, n);
  gensB := TG25_ChooseAbelianGens(B, m);

  images := [];
  for i in [1..n] do
    img := One(B);
    for j in [1..m] do
      if Aeq[j][i] <> 0 then
        img := img * gensB[j]^(Aeq[j][i] mod 4);
      fi;
    od;
    Add(images, img);
  od;

  return rec(A:=A, B:=B, hom:=GroupHomomorphismByImages(A, B, gensA, images));
end;
TG25_IdentityMatMod4 := function(d)
  local M, i, j;
  M := [];
  for i in [1..d] do
    M[i] := [];
    for j in [1..d] do
      if i = j then
        M[i][j] := 1;
      else
        M[i][j] := 0;
      fi;
    od;
  od;
 return M;
end;

TG25_PermMatrixMod4 := function(g)
  local im, M, i;
  im := ListPerm(g, 5);  # im[i]=i^g
  M := List([1..5], i -> List([1..5], j -> 0));
  for i in [1..5] do
    M[i][im[i]] := 1;
  od;
  return M;
end;

# Schreier-style cocycle equations over Z/4 for Z^1 (rows in (Z/4)^(r*d))
TG25_CocycleEquations_Mod4 := function(H, Mgen)
  local gens, r, d, n, elts, m, id, idIdx, visited, Q, head,
        M, C, EqRows, parentIdx, g, i, child, childIdx,
        Calt, D, j, row, t,
        MM, x, y, a, s, rr, cc;

  gens := GeneratorsOfGroup(H);
  r := Length(gens);
  d := Length(Mgen[1]);
  n := r*d;

  elts := Elements(H);
  m := Length(elts);
  id := One(H);
  idIdx := Position(elts, id);

  visited := List([1..m], k -> false);
  Q := []; head := 1;

  M := List([1..m], k -> fail);   # dxd over Z/4
  C := List([1..m], k -> fail);   # nxd over Z/4
  EqRows := [];

  visited[idIdx] := true;
  Add(Q, idIdx);

  M[idIdx] := TG25_IdentityMatMod4(d);
  C[idIdx] := List([1..n], t -> List([1..d], j -> 0));

  while head <= Length(Q) do
    parentIdx := Q[head]; head := head + 1;
    g := elts[parentIdx];

    for i in [1..r] do
      child := g * gens[i];
      childIdx := Position(elts, child);

      # Calt = C[parent] + (block i)*M[parent]
      Calt := List([1..n], t -> ShallowCopy(C[parentIdx][t]));
      for j in [1..d] do
        rr := (i-1)*d + j;
        for cc in [1..d] do
          Calt[rr][cc] := TG25_AddMod4(Calt[rr][cc], M[parentIdx][j][cc]);
        od;
      od;

      if not visited[childIdx] then
        visited[childIdx] := true;
        Add(Q, childIdx);

        # M[child] = M[parent] * Mgen[i]
        MM := List([1..d], x -> List([1..d], y -> 0));
        for x in [1..d] do
          for y in [1..d] do
            s := 0;
            for a in [1..d] do
              s := TG25_AddMod4(s, TG25_MulMod4(M[parentIdx][x][a], Mgen[i][a][y]));
            od;
            MM[x][y] := s;
          od;
        od;

        M[childIdx] := MM;
        C[childIdx] := Calt;

      else
        # D = C[child] - Calt
        D := List([1..n], t -> List([1..d], j -> TG25_SubMod4(C[childIdx][t][j], Calt[t][j])));

        for j in [1..d] do
          row := List([1..n], t -> D[t][j]);
          Add(EqRows, row);
        od;
      fi;
    od;
  od;

  return EqRows;
end;

# Up to maxReps representatives of H^1(H, (Z/4)^d), returned as vectors in (Z/4)^(r*d)
TG25_H1Reps_Mod4 := function(H, Mgen, opts)
  local gens, r, d, n, EqRows, Arec, A, hom, Z1, B1, gensB1,
        j, a, act, diff, x, i, Q, nat, reps, maxReps, eltsQ, eZ, vec, coeff, gensQ, t, gq;

  gens := GeneratorsOfGroup(H);
  r := Length(gens);
  d := Length(Mgen[1]);
  n := r*d;

  maxReps := 32;
  if IsBound(opts.twistMaxReps) then maxReps := opts.twistMaxReps; fi;

  EqRows := TG25_CocycleEquations_Mod4(H, Mgen);

  if Length(EqRows) = 0 then
    A := AbelianGroup(List([1..n], i->4));
    Z1 := A;
  else
    Arec := TG25_HomFromMat_Mod4(EqRows);
    A := Arec.A; hom := Arec.hom;
    Z1 := Kernel(hom);
  fi;

  # coboundaries δ(e_j)
  gensB1 := [];
  for j in [1..d] do
    a := List([1..d], t -> 0); a[j] := 1;
    x := [];
    for i in [1..r] do
      act := TG25_RowTimesMat_Mod4(a, Mgen[i]);
      diff := List([1..d], t -> TG25_SubMod4(a[t], act[t]));
      Append(x, diff);
    od;
    Add(gensB1, TG25_AElemFromVec4(A, x));
  od;

  B1 := Subgroup(A, gensB1);
  B1 := Intersection(B1, Z1);

  nat := NaturalHomomorphismByNormalSubgroup(Z1, B1);
  Q := Image(nat);

  reps := [];
  if Size(Q) <= maxReps then
    eltsQ := Elements(Q);
  else
    gensQ := GeneratorsOfGroup(Q);
    eltsQ := [One(Q)];
    for t in [1..maxReps-1] do
      gq := One(Q);
      for i in [1..Length(gensQ)] do
        coeff := (t + 2*i) mod 4;
        if coeff <> 0 then gq := gq * gensQ[i]^coeff; fi;
      od;
      Add(eltsQ, gq);
    od;
  fi;

  for i in [1..Length(eltsQ)] do
    eZ := PreImagesRepresentative(nat, eltsQ[i]);
    vec := TG25_AVecFromElem4(A, eZ);
    Add(reps, vec);
    if Length(reps) >= maxReps then break; fi;
  od;

  return reps;
end;

# exponent vector v (len 5) -> element in C4^5 using mul2List
TG25_ElemFromVec_Mul2Z4 := function(mul2List, v)
  local e, i;
  e := ();
  for i in [1..5] do
    if v[i] <> 0 then
      e := e * (mul2List[i]^TG25_Mod4(v[i]));
    fi;
  od;
  return e;
end;

# Main: Z/4 cocycle twists + a few kernel seeds (avoid full C4^5)
TG25_Run_Z4_Twists32 := function()
  local p, zList, mul2List, Kseeds, Kseed, Hid, H, td,
        opts, Mgen, repsX, r, i, v, ki, gensTw, G, tid, key, seen, all;

  p := 5;
  zList    := List([0..4], i -> TG25_z(p, i));
  mul2List := List([0..4], i -> TG25_mul2(p, i));

  Kseeds := [];
  Add(Kseeds, rec(name:="seed_none", gens:=[]));
  Add(Kseeds, rec(name:="seed_C4^4_aug", gens:=TG25_MulAugGens(mul2List)));
  Add(Kseeds, rec(name:="seed_ratioC4^4", gens:=GeneratorsOfGroup(TG25_DiagRatio_C4_4(mul2List))));

  opts := rec(twistMaxReps:=32);

  seen := rec();
  all := [];

  for Hid in [1..NrTransitiveGroups(5)] do
    H := TransitiveGroup(5, Hid);

    # plain lift only (perm-module 前提)
    td := TG25_TopLiftDatas5(H, p)[1];

    Mgen := List(GeneratorsOfGroup(H), g -> TG25_PermMatrixMod4(g));
    repsX := TG25_H1Reps_Mod4(H, Mgen, opts);

    r := Length(GeneratorsOfGroup(H));

    for Kseed in Kseeds do
      # plain once
      G := Group(Concatenation(zList, Kseed.gens, td.liftGens));
      tid := TG25_TIDPair(G);
      key := TG25_TIDKey(tid);
      if not IsBound(seen.(key)) then seen.(key) := true; Add(all, tid); fi;

      # twists
      for v in repsX do
        gensTw := [];
        for i in [1..r] do
          ki := TG25_ElemFromVec_Mul2Z4(mul2List, v{[(i-1)*5+1 .. i*5]});
          Add(gensTw, ki * td.liftGens[i]);
        od;
        G := Group(Concatenation(zList, Kseed.gens, gensTw));
        tid := TG25_TIDPair(G);
        key := TG25_TIDKey(tid);
        if not IsBound(seen.(key)) then seen.(key) := true; Add(all, tid); fi;
      od;
    od;

    Print("Hid=", Hid, " |H|=", Size(H), " reps=", Length(repsX), " total=", Length(all), "\n");
  od;

  all := TG25_UniquePairs(all);
  Print("\n=== summary: unique TIDs found (Z/4 cocycle twists up to 32; plain lift; 3 K-seeds) ===\n");
  TG25_PrintPairs("", all);
  return all;
end;
resZ4 := TG25_Run_Z4_Twists32();;
