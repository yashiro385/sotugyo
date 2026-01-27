#############################################################################
# TG49_sylow_side.g
# Degree 49 "Sylow-side" candidate generator (p=7, n=p^2):
#   - Build explicit p-subgroups P_i and P'_i (p-groups in Sym(49))
#   - Enumerate overgroups between P and N_Sym(49)(P)
# Output helpers included.
#############################################################################

TG49_p := 7;
TG49_n := TG49_p^2;

# --- Z_p x Z_p encoding: x = i + j*p (0-based) ---
TG49_IntToPair := function(p, x) return [ x mod p, QuoInt(x, p) ]; end;
TG49_PairToInt := function(p, i, j) return i + j*p; end;

TG49_PermFromMapPair := function(p, fpair)
  local img, x, ij, kl;
  img := [];
  for x in [0..p*p-1] do
    ij := TG49_IntToPair(p, x);
    kl := fpair(ij);               # [i',j'] in 0..p-1
    Add(img, TG49_PairToInt(p, kl[1], kl[2]) + 1);
  od;
  return PermList(img);
end;

# --- basic translations ---
TG49_ti := TG49_PermFromMapPair(TG49_p, ij -> [ (ij[1]+1) mod TG49_p, ij[2] ]); # i+1
TG49_tj := TG49_PermFromMapPair(TG49_p, ij -> [ ij[1], (ij[2]+1) mod TG49_p ]); # j+1

# tau: x -> x+1 mod p^2 on {0..p^2-1}
TG49_tau := PermList(List([0..TG49_n-1], x -> ((x+1) mod TG49_n) + 1));

# z(i0): translate j in fixed block i=i0
TG49_z := function(p, i0)
  return TG49_PermFromMapPair(p,
    function(ij)
      if ij[1] <> i0 then
        return ij;
      fi;
      return [ ij[1], (ij[2]+1) mod p ];
    end
  );
end;

# coefficients a_{r,j} = binom(r,j)*(-1)^(r-j)  (mod p)
TG49_aij := function(r,j)
  if j < 0 or j > r then return 0; fi;
  return Binomial(r,j) * ((-1)^(r-j));
end;

# gamma_i (parameter i=1..p)
TG49_gamma := function(p, i)
  local r, g, j0, e, zj;
  r := p - i;    # 0..p-1
  g := ();
  for j0 in [0..p-1] do
    e := TG49_aij(r, j0) mod p;   # 0..p-1
    if e <> 0 then
      zj := TG49_z(p, j0);
      g := g * (zj^e);
    fi;
  od;
  return g;
end;

# P_i and P'_i
TG49_Pi := function(p, i)
  return Group([ TG49_tau, TG49_gamma(p,i) ]);
end;

TG49_Pprime := function(p, i)
  # (j+1) and (i+1) plus gamma
  return Group([ TG49_tj, TG49_ti, TG49_gamma(p,i) ]);
end;

# --- FULL normalizer lifting: all overgroups between P and N(P) ---
#############################################################################
# FAST normalizer builders for regular groups of degree 49
#   - cyclic regular: P ~= C_49  -> N ~= Hol(C_49) (size 49*42=2058)
#   - elementary abelian regular: P ~= C_7^2 -> N ~= AGL(2,7) (size 49*2016=98784)
#############################################################################

TG49_Sym49 := SymmetricGroup(TG49_n);

TG49_OrderModInt := function(a, m)
  local x, k;
  if GcdInt(a, m) <> 1 then return fail; fi;
  x := a mod m;
  k := 1;
  while x <> 1 do
    x := (x * a) mod m;
    k := k + 1;
    if k > m then return fail; fi;
  od;
  return k;
end;

TG49_PrimitiveUnitMod := function(m)
  local a, ord, phi  ,n, res, p;;

  # We only need m=49 for this project: 3 has order 42 mod 49.
  if m = 49 then
    return 3;
  fi;

  # Generic fallback (in case you reuse this code elsewhere):
  if IsBoundGlobal("PhiInt") then
    phi := ValueGlobal("PhiInt")(m);
  elif IsBoundGlobal("Phi") then
    phi := ValueGlobal("Phi")(m);
  elif IsBoundGlobal("EulerPhi") then
    phi := ValueGlobal("EulerPhi")(m);
  else
    # last resort: compute Euler phi by factoring (slow but avoids missing globals)
  
    n := m; res := m; p := 2;
    while p*p <= n do
      if n mod p = 0 then
        while n mod p = 0 do n := n / p; od;
        res := res - res / p;
      fi;
      p := p + 1;
      while not IsPrimeInt(p) do p := p + 1; od;
    od;
    if n > 1 then res := res - res / n; fi;
    phi := res;
  fi;

  for a in [2..m-1] do
    if GcdInt(a, m) = 1 then
      ord := TG49_OrderModInt(a, m);
      if ord = phi then
        return a;
      fi;
    fi;
  od;

  return fail;
end;


# Build Normalizer of <g> when g is an n-cycle (regular cyclic group of order n)
# using the orbit labeling orb[k+1] = g^k(1).
TG49_NormalizerCyclicRegular := function(g, n)
  local orb, pos, a, img, mult, x;

  orb := Orbit(Group([g]), 1);
  if Length(orb) <> n then
    return fail;
  fi;

  pos := List([1..n], i -> 0);
  for x in [1..n] do
    pos[orb[x]] := x-1;
  od;

  a := TG49_PrimitiveUnitMod(n);
  if a = fail then
    return fail;
  fi;

  img := [];
  for x in [1..n] do
    # x = g^k(1) -> g^(a*k)(1)
    img[x] := orb[((a * pos[x]) mod n) + 1];
  od;
  mult := PermList(img);

  return Group([g, mult]);
end;

# Find 2 generators u,v of an elementary abelian regular group P (size p^2),
# and build the full AGL(2,p) normalizer explicitly from coordinate action.
TG49_NormalizerElemAbelRegular := function(P, p)
  local gens, cand, u, v, U, a, b, tab, inv, idx, pt, g,
        root, ord, A1, A2, A3, lin1, lin2, lin3, img,
        MakeLinPerm;

  if Size(P) <> p^2 then return fail; fi;
  if not IsAbelian(P) then return fail; fi;
  if Exponent(P) <> p then return fail; fi;

  gens := SmallGeneratingSet(P);
  cand := Filtered(gens, x -> Order(x) = p);

  u := fail; v := fail;
  for a in [1..Length(cand)] do
    for b in [a+1..Length(cand)] do
      U := Group([cand[a], cand[b]]);
      if Size(U) = p^2 and IsAbelian(U) then
        u := cand[a];
        v := cand[b];
        break;
      fi;
    od;
    if u <> fail then break; fi;
  od;
  if u = fail then return fail; fi;

  # tab[x + p*y + 1] = 1^(u^x * v^y)
  tab := [];
  for a in [0..p-1] do
    for b in [0..p-1] do
      pt := 1 ^ ( (u^a) * (v^b) );
      tab[a + p*b + 1] := pt;
    od;
  od;

  inv := [];
  for idx in [1..p^2] do
    inv[ tab[idx] ] := idx;
  od;

  MakeLinPerm := function(A)
    local img, pt, t, x, y, x2, y2;
    img := [];
    for pt in [1..p^2] do
      t := inv[pt] - 1;
      x := t mod p;
      y := QuoInt(t, p);
      x2 := (A[1][1]*x + A[1][2]*y) mod p;
      y2 := (A[2][1]*x + A[2][2]*y) mod p;
      img[pt] := tab[x2 + p*y2 + 1];
    od;
    return PermList(img);
  end;

  # find primitive root mod p (order p-1)
  root := fail;
  for g in [2..p-1] do
    ord := TG49_OrderModInt(g, p);
    if ord = p-1 then
      root := g;
      break;
    fi;
  od;
  if root = fail then return fail; fi;

  # Standard generators for GL(2,p):
  # A1 = [[1,1],[0,1]] (shear)
  # A2 = [[0,-1],[1,0]] (rotation)
  # A3 = [[root,0],[0,1]] (scale)
  A1 := [ [1,1], [0,1] ];
  A2 := [ [0, p-1], [1,0] ];
  A3 := [ [root,0], [0,1] ];

  lin1 := MakeLinPerm(A1);
  lin2 := MakeLinPerm(A2);
  lin3 := MakeLinPerm(A3);

  # Normalizer = <P, GL(2,p) generators> acting on the same points
  return Group( Concatenation(GeneratorsOfGroup(P), [lin1, lin2, lin3]) );
end;


#############################################################################
# Replacement: faster overgroup enumeration
#  - build N fast when possible (regular cyclic / regular elem. abelian)
#  - enumerate subgroups of Q=N/P via conjugacy classes reps (fast + less duplicates)
#############################################################################

TG49_Overgroups_FullNormalizer := function(P)
  local N, nat, Q, reps, over, C, g;

  # 1) Try fast normalizer constructions when |P|=49.
  N := fail;

  if Size(P) = TG49_n then
    # cyclic regular case: look for an element of order 49
    g := First(GeneratorsOfGroup(P), x -> Order(x) = TG49_n);
    if g <> fail then
      N := TG49_NormalizerCyclicRegular(g, TG49_n);
    fi;

    # elementary abelian regular case
    if N = fail then
      N := TG49_NormalizerElemAbelRegular(P, TG49_p);
    fi;
  fi;

  # 2) Fallback: real normalizer in Sym(49)
  if N = fail then
    N := Normalizer(TG49_Sym49, P);
  fi;

  # 3) Lift subgroup reps from quotient Q=N/P.
  nat := NaturalHomomorphismByNormalSubgroup(N, P);
  Q := Image(nat);

  # Prefer conjugacy class representatives (much less than AllSubgroups).
  reps := List(ConjugacyClassesSubgroups(Q), Representative);

  over := [];
  for C in reps do
    Add(over, PreImage(nat, C));
  od;

  return over;
end;


# --- main: Sylow-side candidates ---
TG49_SylowSideCandidates := function()
  local p, out, i;
  p := TG49_p;
  out := [];
  for i in [1..p] do
    Append(out, TG49_Overgroups_FullNormalizer(TG49_Pi(p,i)));
  od;
  for i in [1..p] do
    Append(out, TG49_Overgroups_FullNormalizer(TG49_Pprime(p,i)));
  od;
  return out;
end;

# --- optional: reduce duplicates by TransitiveIdentification ---
TG49_TIDIndex := function(G)
  local tid;
  tid := TransitiveIdentification(G);
  if IsList(tid) then
    return tid[2];
  else
    return tid;   # integer id
  fi;
end;

TG49_UniqueByTI := function(Gs)
  local seen, out, G, k;
  seen := [];
  out := [];
  for G in Gs do
    k := TG49_TIDIndex(G);
    if not k in seen then
      Add(seen, k);
      Add(out, G);
    fi;
  od;
  return out;
end;


# --- writer: records rec(sizeG, gens) ---
TG49_WriteCandidates := function(outFile, Gs, src)
  local G, gs, i;
  PrintTo(outFile, "# AUTOGENERATED\n");
  if src <> fail then
    AppendTo(outFile, "# src=", src, "\n");
  fi;
  AppendTo(outFile, "TG49_Candidates := [];\n\n");
  for G in Gs do
    gs := SmallGeneratingSet(G);
    AppendTo(outFile,
      "Add(TG49_Candidates, rec(sizeG:=", String(Size(G)), ", gens:=["
    );
    for i in [1..Length(gs)] do
      AppendTo(outFile, String(gs[i]));
      if i < Length(gs) then AppendTo(outFile, ","); fi;
    od;
    AppendTo(outFile, "]));\n");
  od;
  AppendTo(outFile, "\nreturn TG49_Candidates;\n");
end;

# Print like:
# === summary: unique TIDs found (this scan) ===
# [ [49, 2], [49, 3], ... ]


# example:
 Gs := TG49_SylowSideCandidates();
 TG49_WriteCandidates("tg49_sylow_recs.g", Gs, "sylow_fastN");


#############################################################################
# Example run (uncomment in your driver):
#
# Gs := TG49_SylowSideCandidates();
# Print("raw=", Length(Gs), "\n");
# GsU := TG49_UniqueByTI(Gs);
# Print("unique(TI)=", Length(GsU), "\n");
# TG49_WriteCandidates("TG49_sylow_candidates.g", GsU, "sylow_fullN");
#############################################################################
