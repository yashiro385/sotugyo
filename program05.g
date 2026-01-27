#############################################################################
# saigo_invsubspaces49_fixed.g  (degree 49 = 7^2)
#
# 49-spec:
#   - Aut(C7) = C6: diagonal layer uses order-6 within-block multipliers.
#   - No TransitiveIdentification / TID verification.
#   - Output records only: rec(size:=..., gen:=[...]).
#
# Minimal runner provided:
#   recs := TG49_Run_Fill123_C6(rec(dedup:=true));;
#   TG49_SaveRecs("tg49_out.g", recs);;
#############################################################################

TG49_NO_AUTORUN := true;;

#############################################################################
# Constants
#############################################################################
TG49_p := 7;;
TG49_n := 49;;
TG49_mulGen := 3;;  # generator of F_7^* (order 6)

#############################################################################
# Basic permutation constructors for the Z_p \wr S_p model (points 1..p^2)
# Encode points as x = i + j*p with i,j in 0..p-1, mapped to x+1.
#############################################################################

TG49_WithinPerm_Inversion := function(p)
  local img, j;
  img := [];
  for j in [0..p-1] do
    Add(img, ((-j) mod p) + 1);
  od;
  return PermList(img);
end;

TG49_WithinPerm_MulGen := function(p, a)
  local img, j;
  img := [];
  for j in [0..p-1] do
    Add(img, ((a*j) mod p) + 1);
  od;
  return PermList(img);
end;

TG49_LiftWithin := function(p, sig, i0)
  # apply within-block permutation sig to block i0 (0..p-1)
  local img, x, i, j, jj;
  img := [];
  for x in [0..p*p-1] do
    i := x mod p;
    j := QuoInt(x, p);
    if i = i0 then
      jj := ((j+1)^sig) - 1;
      Add(img, i + jj*p + 1);
    else
      Add(img, x + 1);
    fi;
  od;
  return PermList(img);
end;

TG49_LiftBlocks := function(p, h)
  # lift a block permutation h in Sym(p) to degree p^2
  local imH, img, x, i, j, ii;
  imH := ListPerm(h, p);
  img := [];
  for x in [0..p*p-1] do
    i := x mod p;
    j := QuoInt(x, p);
    ii := imH[i+1] - 1;
    Add(img, ii + j*p + 1);
  od;
  return PermList(img);
end;

TG49_LiftBlocks_WithWithin := function(p, h, withinList, where)
  # where in {"dest","src"}; withinList is length p of within-block perms
  local imH, img, x, i, j, ii, w, imW, jp;
  imH := ListPerm(h, p);
  img := [];
  for x in [0..p*p-1] do
    i := x mod p;
    j := QuoInt(x, p);
    ii := imH[i+1] - 1;
    if where = "dest" then
      w := withinList[ii+1];
    else
      w := withinList[i+1];
    fi;
    imW := ListPerm(w, p);
    jp  := imW[j+1];
    Add(img, ii + (jp-1)*p + 1);
  od;
  return PermList(img);
end;

#############################################################################
# Generators for base C7^7 (translations), inv-layer C2^7, mul-layer C6^7
#############################################################################

TG49_z := function(p, i0)
  return TG49_LiftWithin(p, PermList(Concatenation([2..p],[1])), i0);
end;

TG49_inv := function(p, i0)
  return TG49_LiftWithin(p, TG49_WithinPerm_Inversion(p), i0);
end;

TG49_mul3 := function(p, i0)
  return TG49_LiftWithin(p, TG49_WithinPerm_MulGen(p, TG49_mulGen), i0);
end;

#############################################################################
# Module / MeatAxe helpers
#############################################################################

TG49_PermMatrix := function(F, g, p)
  local M, i, img;
  M := List([1..p], x -> List([1..p], y -> Zero(F)));
  for i in [1..p] do
    img := i^g;
    M[i][img] := One(F);
  od;
  return Matrix(F, M);
end;

TG49_BasisVectorsOfSubmodule := function(s)
  # MeatAxe submodule basis object -> list of vectors
  if IsList(s) then
    return s;
  fi;
  if IsBoundGlobal("Basis") then
    return BasisVectors(Basis(s));
  fi;
  return fail;
end;

TG49_InvariantSubmoduleBases := function(H, F, opts)
  local p, gens, mats, modd, subs, maxSub, maxDim, out, s, vecs, dim;

  p := TG49_p;

  if not IsBoundGlobal("MTX") then
    Error("MeatAxe (MTX) is not available.");
  fi;

  gens := GeneratorsOfGroup(H);
  mats := List(gens, g -> TG49_PermMatrix(F, g, p));

 
    modd := GModuleByMats(mats, F);
 

  if not IsBound(opts) then opts := rec(); fi;
  maxSub := fail;
  if IsBound(opts.maxSub) then maxSub := opts.maxSub; fi;
  maxDim := fail;
  if IsBound(opts.maxDim) then maxDim := opts.maxDim; fi;

  # Prefer BasesSubmodules; if unavailable, try Submodules.
  if IsBound(MTX.BasesSubmodules) then
    subs := MTX.BasesSubmodules(modd);
  elif IsBound(MTX.Submodules) then
    subs := MTX.Submodules(modd);
  else
    Error("No MTX submodule enumerator found (need MTX.BasesSubmodules or MTX.Submodules).");
  fi;

  if maxSub <> fail and Length(subs) > maxSub then
    subs := subs{[1..maxSub]};
  fi;

  out := [];
  for s in subs do
    vecs := TG49_BasisVectorsOfSubmodule(s);
    if vecs = fail then
      continue;
    fi;
    dim := Length(vecs);
    if maxDim <> fail and dim > maxDim then
      continue;
    fi;
    Add(out, vecs);
  od;

  return out;
end;

#############################################################################
# Convert rows -> subgroup in Sym(49)
#############################################################################

TG49_TransFromRow := function(zList, row, p)
  local g, i, c;
  g := ();
  for i in [1..Length(zList)] do
    c := IntFFE(row[i]) mod p;
    if c <> 0 then
      g := g * (zList[i]^c);
    fi;
  od;
  return g;
end;

TG49_SubgroupFromRows_Cp := function(zList, rows, p)
  local gens, r;
  gens := [];
  for r in rows do
    Add(gens, TG49_TransFromRow(zList, r, p));
  od;
  if Length(gens) = 0 then
    return Group(());
  fi;
  return Group(gens);
end;

TG49_SubgroupFromRows_C2 := function(invList, rows)
  local gens, r, g, i, bit;
  gens := [];
  for r in rows do
    g := ();
    for i in [1..Length(invList)] do
      bit := IntFFE(r[i]) mod 2;
      if bit = 1 then g := g * invList[i]; fi;
    od;
    Add(gens, g);
  od;
  if Length(gens) = 0 then return Group(()); fi;
  return Group(gens);
end;

TG49_SubgroupFromRows_C2_fromMul3 := function(mul3List, rows)
  # Use the order-2 part of C6: g^3.
  local gens, r, g, i, bit;
  gens := [];
  for r in rows do
    g := ();
    for i in [1..Length(mul3List)] do
      bit := IntFFE(r[i]) mod 2;
      if bit = 1 then g := g * (mul3List[i]^3); fi;
    od;
    Add(gens, g);
  od;
  if Length(gens) = 0 then return Group(()); fi;
  return Group(gens);
end;

TG49_SubgroupFromRows_C3_fromMul3 := function(mul3List, rows)
  # Use the order-3 part of C6: g^2.
  local gens, r, g, i, c;
  gens := [];
  for r in rows do
    g := ();
    for i in [1..Length(mul3List)] do
      c := IntFFE(r[i]) mod 3;
      if c <> 0 then g := g * ((mul3List[i]^2)^c); fi;
    od;
    Add(gens, g);
  od;
  if Length(gens) = 0 then return Group(()); fi;
  return Group(gens);
end;

#############################################################################
# Standard diagonal ratio subgroup C6^6 and small variants
#############################################################################

TG49_DiagRatio_C6_6 := function(mul3List)
  local gens, i, last;
  gens := [];
  last := mul3List[Length(mul3List)];
  for i in [1..Length(mul3List)-1] do
    Add(gens, mul3List[i] * (last^-1));
  od;
  return Group(gens);
end;

TG49_DiagRatio_C6_6_xC2 := function(mul3List)
  local R, last;
  R := TG49_DiagRatio_C6_6(mul3List);
  last := mul3List[Length(mul3List)];
  return Group(Concatenation(GeneratorsOfGroup(R), [last^3]));
end;

TG49_DiagRatio_C6_6_xC3 := function(mul3List)
  local R, last;
  R := TG49_DiagRatio_C6_6(mul3List);
  last := mul3List[Length(mul3List)];
  return Group(Concatenation(GeneratorsOfGroup(R), [last^2]));
end;

#############################################################################
# Top lift variants (5 fixed variants, but only plain is used by default)
#############################################################################

TG49_TopLiftData := function(H, p, name, withinList, where)
  local gensH, liftGens;
  gensH := GeneratorsOfGroup(H);
  liftGens := List(gensH, g -> TG49_LiftBlocks_WithWithin(p, g, withinList, where));
  return rec(name:=name, Top:=Group(liftGens), liftGens:=liftGens);
end;

TG49_TopLiftDatas5 := function(H, p)
  local wId, wMul, wInv, W, where, names, out, i, exps;

  wId  := ();
  wMul := TG49_WithinPerm_MulGen(p, TG49_mulGen);  # order 6
  wInv := TG49_WithinPerm_Inversion(p);            # order 2

  # Variant patterns: each entry is a list of length p of within-block perms.
  exps := List([0..p-1], t -> (t mod 6));

  W := [
    List([1..p], i->wId),
    List([1..p], i->wMul),
    List([1..p], i->wInv),
    List([1..p], i->(wMul^exps[i])),
    List([1..p], i->(wMul^((2*exps[i]) mod 6)))
  ];

  where := ["dest","dest","dest","dest","src"];
  names := ["plain","dest_mul","dest_inv","dest_diagPow","src_mixPow"];

  out := [];
  for i in [1..5] do
    Add(out, TG49_TopLiftData(H, p, names[i], W[i], where[i]));
  od;

  return out;
end;

#############################################################################
# Candidate generation layers (1)(2)(3)
#############################################################################

TG49_Cands_1_PermModule_GF7 := function(H, zList, Top, opts)
  local F, out, bases, rows, K, G;
  F := GF(7);
  out := [];
  bases := TG49_InvariantSubmoduleBases(H, F, opts);
  for rows in bases do
    K := TG49_SubgroupFromRows_Cp(zList, rows, 7);
    if Size(K) = 1 then
      continue;
    fi;
    G := Group(Concatenation(GeneratorsOfGroup(K), GeneratorsOfGroup(Top)));
    Add(out, G);
  od;
  return out;
end;

TG49_Cands_2_Twist_C2_Inv_GF2 := function(H, zList, invList, Top, opts)
  local F, out, bases, rows, E, G;
  F := GF(2);
  out := [];
  bases := TG49_InvariantSubmoduleBases(H, F, opts);
  for rows in bases do
    E := TG49_SubgroupFromRows_C2(invList, rows);
    G := Group(Concatenation(zList, GeneratorsOfGroup(E), GeneratorsOfGroup(Top)));
    Add(out, G);
  od;
  return out;
end;

TG49_Cands_3_Diagonal_C6 := function(H, zList, invList, mul3List, Top, opts)
  local out, R, Rx2, Rx3, bases2, bases3, rows, D2, D3, withInv;

  out := [];

  R   := TG49_DiagRatio_C6_6(mul3List);
  Rx2 := TG49_DiagRatio_C6_6_xC2(mul3List);
  Rx3 := TG49_DiagRatio_C6_6_xC3(mul3List);

  Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R),   GeneratorsOfGroup(Top))));
  Add(out, Group(Concatenation(zList, GeneratorsOfGroup(Rx2), GeneratorsOfGroup(Top))));
  Add(out, Group(Concatenation(zList, GeneratorsOfGroup(Rx3), GeneratorsOfGroup(Top))));

  # 2-part (C2^7) inside C6^7 from GF(2)^7 invariants
  bases2 := TG49_InvariantSubmoduleBases(H, GF(2), opts);
  for rows in bases2 do
    D2 := TG49_SubgroupFromRows_C2_fromMul3(mul3List, rows);
    Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R), GeneratorsOfGroup(D2), GeneratorsOfGroup(Top))));
  od;

  # 3-part (C3^7) inside C6^7 from GF(3)^7 invariants
  bases3 := TG49_InvariantSubmoduleBases(H, GF(3), opts);
  for rows in bases3 do
    D3 := TG49_SubgroupFromRows_C3_fromMul3(mul3List, rows);
    Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R), GeneratorsOfGroup(D3), GeneratorsOfGroup(Top))));
  od;

  withInv := false;
  if IsBound(opts.doDiagWithInv) and opts.doDiagWithInv = true then
    withInv := true;
  fi;
  if withInv then
    # Reuse GF(2)^7 bases to add an inversion layer in the same pattern.
    for rows in bases2 do
      D2 := TG49_SubgroupFromRows_C2_fromMul3(mul3List, rows);
      Add(out, Group(Concatenation(zList, GeneratorsOfGroup(R), GeneratorsOfGroup(D2), invList, GeneratorsOfGroup(Top))));
    od;
  fi;

  return out;
end;

#############################################################################
# Record export (size + gen only), optional cheap dedup
#############################################################################

TG49_HashPermImages := function(g, n)
  local h, i;
  h := 0;
  for i in [1..n] do
    h := (h * 911382323 + (i^g)) mod 2147483647;
  od;
  if h < 0 then h := -h; fi;
  return h;
end;

TG49_KeyFromGroup := function(G)
  local gens, hs, h, n;
  n := TG49_n;
  gens := GeneratorsOfGroup(G);
  hs := List(gens, gg -> TG49_HashPermImages(gg, n));
  Sort(hs);
  return Concatenation(String(Size(G)), ":", String(hs));
end;

TG49_RecsFromGroups := function(groups, opts)
  local out, seen, doDedup, G, key;
  out := [];
  seen := rec();
  doDedup := true;
  if IsBound(opts.dedup) then doDedup := opts.dedup; fi;

  for G in groups do
    if not IsTransitive(G, [1..TG49_n]) then
      continue;
    fi;

    if doDedup then
      key := TG49_KeyFromGroup(G);
      if IsBound(seen.(key)) then
        continue;
      fi;
      seen.(key) := true;
    fi;

    Add(out, rec(size:=Size(G), gen:=GeneratorsOfGroup(G)));
  od;

  return out;
end;

TG49_SaveRecs := function(outFile, recs)
  local f, r;
  f := OutputTextFile(outFile, false);
  SetPrintFormattingStatus(f, false);
  AppendTo(f, "recs := [\n");
  for r in recs do
    AppendTo(f, "  rec(size:=", String(r.size), ", gen:=", String(r.gen), "),\n");
  od;
  AppendTo(f, "];\n");
  CloseStream(f);
end;

#############################################################################
# One-pass runner (layers 1-3, C6 diagonal), returns list of recs
#############################################################################

TG49_Run_Fill123_C6 := function(opts)
  local p, n, zList, invList, mul3List, Hs, Hid, H,
        TopDatas, td, Top, all, do1, do2, do3, doAllLifts;

  if not IsBound(opts) then opts := rec(); fi;

  p := TG49_p;
  n := TG49_n;

  do1 := true; do2 := true; do3 := true;
  if IsBound(opts.do1) then do1 := opts.do1; fi;
  if IsBound(opts.do2) then do2 := opts.do2; fi;
  if IsBound(opts.do3) then do3 := opts.do3; fi;

  doAllLifts := false;
  if IsBound(opts.doAllTopLifts) then doAllLifts := opts.doAllTopLifts; fi;

  zList    := List([0..p-1], i0 -> TG49_z(p, i0));
  invList  := List([0..p-1], i0 -> TG49_inv(p, i0));
  mul3List := List([0..p-1], i0 -> TG49_mul3(p, i0));

  Hs := List([1..NrTransitiveGroups(p)], k -> TransitiveGroup(p, k));

  all := [];
  for Hid in [1..Length(Hs)] do
    H := Hs[Hid];

    TopDatas := TG49_TopLiftDatas5(H, p);
    if not doAllLifts then
      TopDatas := Filtered(TopDatas, td -> td.name = "plain");
    fi;

    for td in TopDatas do
      Top := td.Top;
      if do1 then Append(all, TG49_Cands_1_PermModule_GF7(H, zList, Top, opts)); fi;
      if do2 then Append(all, TG49_Cands_2_Twist_C2_Inv_GF2(H, zList, invList, Top, opts)); fi;
      if do3 then Append(all, TG49_Cands_3_Diagonal_C6(H, zList, invList, mul3List, Top, opts)); fi;
    od;
  od;

  return TG49_RecsFromGroups(all, opts);
end;

#############################################################################
# Optional autorun (disabled by default)
#############################################################################

  TG49_SaveRecs("tg49_out.g", TG49_Run_Fill123_C6(rec(dedup:=true)));


#############################################################################
# End of file
#############################################################################
