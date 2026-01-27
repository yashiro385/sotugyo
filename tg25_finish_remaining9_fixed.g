#############################################################################
# tg25_finish_remaining9.g
#
# Goal: try to hit the remaining TIDs:
#   [25,121], [25,132], [25,141], [25,147], [25,149],
#   [25,162], [25,164], [25,167], [25,170]
#
# This file is meant to be read AFTER your base scanner file, e.g.:
#   TG25_NO_AUTORUN := true;;
#   Read("saigo_invsubspaces32_fixed.g");;
#   Read("tg25_finish_remaining9.g");;
#   TG25_Run_Remaining9();;
#############################################################################

#############################################################################
# 0) small helpers
#############################################################################

TG25_ZAugGens := function(zList)
  # augmentation submodule of C5^5 (size 5^4)
  return List([1..4], i -> zList[i] * zList[5]^-1);
end;

TG25_IntModP := function(x, p)
  local t;
  if IsFFE(x) then
    t := IntFFE(x);
  else
    t := x;
  fi;
  t := t mod p;
  if t < 0 then t := t + p; fi;
  return t;
end;

TG25_ElemFromVec_Z := function(zList, v, p)
  local e, i, c;
  e := ();
  for i in [1..5] do
    c := TG25_IntModP(v[i], p);
    if c <> 0 then
      e := e * (zList[i]^c);
    fi;
  od;
  return e;
end;

TG25_InTargets := function(tid, targets)
  return tid in targets;
end;

TG25_RemoveTarget := function(tid, targets)
  return Filtered(targets, x -> x <> tid);
end;

#############################################################################
# 1) extend kernel variants by adding C5^4 (augmentation) kernel
#############################################################################

TG25_KernelVariants_Extended := function(zList, invList, mul2List)
  local out;
  out := TG25_KernelVariants(zList, invList, mul2List);
  Add(out, rec(name:="K_C5^4_aug", gens:=TG25_ZAugGens(zList), invMode:="none"));
  return out;
end;

#############################################################################
# 2) Z/4 cohomology (copied from saigo_z4_addon_fixed.g + z4_hom_patch.g,
#    and slightly generalized by using all 5 lifts later)
#############################################################################

TG25_Mod4 := function(x)
  x := x mod 4;
  if x < 0 then x := x + 4; fi;
  return x;
end;

TG25_AddMod4 := function(a,b) return TG25_Mod4(a+b); end;
TG25_SubMod4 := function(a,b) return TG25_Mod4(a-b); end;
TG25_MulMod4 := function(a,b) return TG25_Mod4(a*b); end;

TG25_PermMatrixMod4 := function(g)
  local d, M, i, j, img;
  d := 5;
  M := List([1..d], i -> List([1..d], j -> 0));
  for i in [1..d] do
    img := i^g;
    M[i][img] := 1;
  od;
  return M;
end;

TG25_AVecFromElem4 := function(A, e)
  # For A = (C4)^n etc., pcgs-exponents are the coordinate vector.
  return ExponentsOfPcElement(Pcgs(A), e);
end;

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

  visited := List([1..m], i -> false);
  visited[idIdx] := true;
  Q := [idIdx];
  head := 1;

  # M[g] = action matrix of g on module, mod 4
  M := List([1..m], i -> List([1..d], x -> List([1..d], y -> 0)));
  for x in [1..d] do M[idIdx][x][x] := 1; od;

  # C[g] = coefficient matrix expressing cocycle value at g in terms of
  # unknowns (v_1,...,v_r), each v_i in Z4^d.
  # Represented as n vectors of length d.
  C := List([1..m], i -> fail);
  C[idIdx] := List([1..n], t -> List([1..d], j -> 0));

  EqRows := [];

  while head <= Length(Q) do
    parentIdx := Q[head]; head := head + 1;
    g := elts[parentIdx];

    for i in [1..r] do
      child := g * gens[i];
      childIdx := Position(elts, child);

      # Calt = C[parent] + (block i) * M[parent]
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
        # D = C[child] - Calt gives linear constraints
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

TG25_ChooseAbelianGens := function(G, expected)
  local gens;

  gens := fail;

  if IsBoundGlobal("IndependentGeneratorsOfAbelianGroup") then
    if HasIsAbelian(G) and IsAbelian(G) then
      gens := IndependentGeneratorsOfAbelianGroup(G);
    fi;
  fi;

  if gens = fail then
    gens := GeneratorsOfGroup(G);
  fi;

  if Length(gens) < expected then
    # pad with identity (should not happen often; but keeps lengths consistent)
    while Length(gens) < expected do Add(gens, One(G)); od;
  fi;

  if Length(gens) > expected then
    gens := gens{[1..expected]};
  fi;

  return gens;
end;

TG25_HomFromMat_Mod4 := function(Aeq)
  local m, n, A, B, gensA, gensB, images, i, j, img;

  m := Length(Aeq);
  if m = 0 then
    Error("Aeq has 0 rows");
  fi;
  n := Length(Aeq[1]);

  A := AbelianGroup(List([1..n], i -> 4));
  B := AbelianGroup(List([1..m], i -> 4));

  gensA := TG25_ChooseAbelianGens(A, n);
  gensB := TG25_ChooseAbelianGens(B, m);

  images := [];
  for i in [1..n] do
    img := One(B);
    for j in [1..m] do
      if Aeq[j][i] <> 0 then
        img := img * gensB[j]^TG25_Mod4(Aeq[j][i]);
      fi;
    od;
    Add(images, img);
  od;

  return GroupHomomorphismByImages(A, B, gensA, images);
end;

TG25_H1Reps_Mod4 := function(H, Mgen, opts)
  local gens, r, d, n, EqRows, Arec, A, hom, Z1, gensA, B1, gensB1,y,
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
    hom := TG25_HomFromMat_Mod4(EqRows);
    A := Source(hom);
    Z1 := Kernel(hom);
  fi;

  gensA := TG25_ChooseAbelianGens(A, n);

  # coboundaries B1 = { (a^g_i - a) } for a in module
  B1 := [];
  for j in [1..d] do
    # basis element e_j in Z4^d
    a := List([1..d], x -> 0); a[j] := 1;

    # for each generator g_i, compute a^g_i - a
    diff := [];
    for i in [1..r] do
      act := List([1..d], x -> 0);
      for x in [1..d] do
        for y in [1..d] do
          act[y] := TG25_AddMod4(act[y], TG25_MulMod4(a[x], Mgen[i][x][y]));
        od;
      od;
      Append(diff, List([1..d], x -> TG25_SubMod4(act[x], a[x])));
    od;
    Add(B1, diff);
  od;

  gensB1 := [];
  for x in B1 do
    Add(gensB1, Product(List([1..n], i -> gensA[i]^TG25_Mod4(x[i]))));
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

#############################################################################
# 3) Main driver: try to hit the remaining 9 targets
#############################################################################


TG25_LiftLabel := function(td)
  if IsRecord(td) then
    if IsBound(td.mode) then return td.mode; fi;
    if IsBound(td.name) then return td.name; fi;
    if IsBound(td.where) then return td.where; fi;
    if IsBound(td.kind) then return td.kind; fi;
  fi;
  return "lift";
end;

TG25_Run_Remaining9 := function()
  local p, targets, need, found, zList, invList, mul2List, Kvars,
        Hid, H, TopDatas, td, kv, G, tid,
        F2, F5, opts2, opts5, Mgen2, Mgen5, reps2, reps5,
        optsZ4, MgenZ4, repsZ4, twisted, gensTw, v, i, r, ki, block,
        details;

  p := 5;

  targets := [
    [25,121],[25,132],[25,141],[25,147],[25,149],
    [25,162],[25,164],[25,167],[25,170]
  ];

  need := ShallowCopy(targets);
  found := [];

  zList    := List([0..4], i -> TG25_z(p, i));
  invList  := List([0..4], i -> TG25_inv(p, i));
  mul2List := List([0..4], i -> TG25_mul2(p, i));

  Kvars := TG25_KernelVariants_Extended(zList, invList, mul2List);

  F2 := GF(2);
  F5 := GF(5);

  opts2 := rec(twistMaxReps:=4096, twistSkipZero:=true, twistMode:="lex");
  opts5 := rec(twistMaxReps:=4096, twistSkipZero:=true, twistMode:="lex");
  optsZ4 := rec(twistMaxReps:=1024);

  # Only H with possible remaining: D10, F20, S5
  for Hid in [2,3,5] do
    H := TransitiveGroup(5, Hid);
    r := Length(GeneratorsOfGroup(H));

    TopDatas := TG25_TopLiftDatas5(H, p);

    # GF(2) H^1 reps for inv / mul2sq twists
    Mgen2 := TG25_ActionMats_PermModule(H, F2);
    reps2 := TG25_H1Reps_Module_Schreier(H, F2, Mgen2, opts2);

    # GF(5) translation H^1 reps (mainly for Hid=5 / S5)
    Mgen5 := TG25_ActionMats_PermModule(H, F5);
    reps5 := TG25_H1Reps_Module_Schreier(H, F5, Mgen5, opts5);

    # Z/4 H^1 reps for mul2 twists (C4-layer)
    MgenZ4 := List(GeneratorsOfGroup(H), g -> TG25_PermMatrixMod4(g));
    repsZ4 := TG25_H1Reps_Mod4(H, MgenZ4, optsZ4);

    Print("\n=== Hid=", Hid, " |H|=", Size(H),
          " lifts=", Length(TopDatas),
          " reps2=", Length(reps2),
          " reps5=", Length(reps5),
          " repsZ4=", Length(repsZ4), " ===\n");

    for td in TopDatas do
      for kv in Kvars do
        # (A) plain
        G := Group(Concatenation(kv.gens, td.liftGens));
        tid := TG25_TIDPair(G);
        if TG25_InTargets(tid, need) then
          details := rec(tid:=tid, Hid:=Hid, lift:=TG25_LiftLabel(td), K:=kv.name, twist:="plain");
          Add(found, details);
          need := TG25_RemoveTarget(tid, need);
          Print("HIT ", tid, " via ", details, "\n");
          if Length(need)=0 then
            Print("\nALL TARGETS HIT.\n");
            return found;
          fi;
        fi;

        # (B) GF(2) twists for inv / mul2sq modes
        if kv.invMode <> "none" then
          twisted := TG25_TwistLiftGens_FromH1(H, td.liftGens, kv.invMode, invList, mul2List, reps2);
          for gensTw in twisted do
            G := Group(Concatenation(kv.gens, gensTw));
            tid := TG25_TIDPair(G);
            if TG25_InTargets(tid, need) then
              details := rec(tid:=tid, Hid:=Hid, lift:=TG25_LiftLabel(td), K:=kv.name, twist:=Concatenation("GF2/", kv.invMode));
              Add(found, details);
              need := TG25_RemoveTarget(tid, need);
              Print("HIT ", tid, " via ", details, "\n");
              if Length(need)=0 then
                Print("\nALL TARGETS HIT.\n");
                return found;
              fi;
            fi;
          od;
        fi;


        # (D) GF(5) translation twists: only when kv actually contains C5 translations
        if kv.name <> "K_C5^4_aug" then
          for v in reps5 do
            gensTw := [];
            for i in [1..r] do
              block := v{[(i-1)*5+1 .. i*5]};
              ki := TG25_ElemFromVec_Z(zList, block, p);
              Add(gensTw, ki * td.liftGens[i]);
            od;
            G := Group(Concatenation(kv.gens, gensTw));
            tid := TG25_TIDPair(G);
            if TG25_InTargets(tid, need) then
              details := rec(tid:=tid, Hid:=Hid, lift:=TG25_LiftLabel(td), K:=kv.name, twist:="GF5/z");
              Add(found, details);
              need := TG25_RemoveTarget(tid, need);
              Print("HIT ", tid, " via ", details, "\n");
              if Length(need)=0 then
                Print("\nALL TARGETS HIT.\n");
                return found;
              fi;
            fi;
          od;
        fi;

      od;
    od;
  od;

  Print("\n=== DONE. targets hit: ", Length(found), "/", Length(targets), " ===\n");
  Print("hit details:\n", found, "\n");
  Print("still missing:\n", need, "\n");
  return rec(hit:=found, missing:=need);
end;

#############################################################################
# end
#############################################################################
Read("saigo_invsubspaces32_fixed.g");;
   TG25_Run_Remaining9();;