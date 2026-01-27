########################################################################
##
##  G49_generate_from_Hsubspaces_fixed.g
##
##  Input expected in current directory:
##    - tg49_Hsubspaces.g
##        TG49_HSubspaces := [ rec(
##            tid := [7,k], size := |H|,
##            Hgens := [perm on 7 points, ...],
##            subspaces := [ rec(key:=..., dim:=..., basis:=<int rows>, tag:=...), ...]
##          ), ... ];
##
##  Output:
##    - functions to build candidate groups of degree 49:
##        * CountTG49_Subspaces()
##        * CountTG49_SubspacesByH()
##        * EnumerateG49_FromAllSubspaces()   (returns list of groups)
##        * EnumerateG49_FromAllSubspaces_Info() (returns list of records)
##
########################################################################

if not IsBound(p) then p := 7; fi;   # block size
if not IsBound(m) then m := 7; fi;   # number of blocks (n = 49)

#############################################################################
## 0. Load mined H-subspaces
#############################################################################

EnsureTG49_HSubspaces := function()
  if IsBound(TG49_HSubspaces) and Length(TG49_HSubspaces) > 0 then
    return;
  fi;
  if Filename(DirectoryCurrent(), "tg49_Hsubspaces.g") = fail then
    Error("tg49_Hsubspaces.g not found in current directory");
  fi;
  Read("tg49_Hsubspaces.g");
  if not IsBound(TG49_HSubspaces) or Length(TG49_HSubspaces) = 0 then
    Error("tg49_Hsubspaces.g loaded but TG49_HSubspaces is empty");
  fi;
end;

#############################################################################
## 1. Basic permutation lifts
#############################################################################

# embed perm on {1..p} into i-th block of size p inside {1..p*m}
LiftToBlockPerm := function(perm, i, p_, m_)
  local n_, img, k, off;
  n_  := p_ * m_;
  off := (i-1) * p_;
  img := [1..n_];
  for k in [1..p_] do
    img[off+k] := off + (k ^ perm);
  od;
  return PermList(img);
end;

# lift block permutation h on {1..m} to {1..p*m} by permuting blocks
BlockPerm := function(h, p_, m_)
  local n_, img, b, k, sb, db;
  n_  := p_ * m_;
  img := [1..n_];
  for b in [1..m_] do
    sb := (b-1) * p_;
    db := ((b ^ h) - 1) * p_;
    for k in [1..p_] do
      img[sb+k] := db + k;
    od;
  od;
  return PermList(img);
end;

DegreeOfGroup := function(G)
  local gens, d, g, lg;
  if IsTrivial(G) then return 1; fi;
  gens := GeneratorsOfGroup(G);
  d := 0;
  for g in gens do
    lg := LargestMovedPoint(g);
    if lg > d then d := lg; fi;
  od;
  if d = 0 then return 1; fi;
  return d;
end;

#############################################################################
## 2. Basis access (compat)
#############################################################################

BasisIntFromSub := function(sub)
  if IsBound(sub.Bint) then
    return sub.Bint;           # legacy
  elif IsBound(sub.basis) then
    return sub.basis;          # current
  elif IsBound(sub.B) then
    return sub.B;              # fallback
  fi;
  return fail;
end;

#############################################################################
## 3. Kernel from an H-invariant subspace of (C_p)^m
#############################################################################

# Use the standard p-cycle a=(1..p) inside each block.
# For each row u in the basis (integers mod p), build
#   el_u = Π_i  a_i^{u[i]}  (embedded in block i)
# and let K = < el_u : u in basis >.

KernelFromSubspace_CpPower := function(p_, m_, Bint)
  local a, gensK, u, el, i, e;

  if Bint = fail then
    Error("KernelFromSubspace_CpPower: missing basis");
  fi;

  a := ();
  # build a=(1,2,...,p_)
  a := PermList(Concatenation([2..p_],[1]));

  gensK := [];
  for u in Bint do
    el := ();
    for i in [1..m_] do
      e := u[i] mod p_;
      if e <> 0 then
        el := el * LiftToBlockPerm(a^e, i, p_, m_);
      fi;
    od;
    if el <> () then
      Add(gensK, el);
    fi;
  od;

  if Length(gensK) = 0 then
    return Group([()]);
  fi;
  return Group(gensK);
end;

#############################################################################
## 4. Lift H (on blocks) and build G = K ⋊ H
#############################################################################

LiftH_Block := function(recH, p_, m_)
  local lifts, h;
  if not IsBound(recH.Hgens) then
    Error("LiftH_Block: recH has no .Hgens");
  fi;
  lifts := [];
  for h in recH.Hgens do
    Add(lifts, BlockPerm(h, p_, m_));
  od;
  return lifts;
end;

G49_FromSubspaceRec := function(recH, sub)
  local Bint, K, liftsH, gens, G;

  Bint := BasisIntFromSub(sub);
  if Bint = fail then
    Error("G49_FromSubspaceRec: sub has no basis field (expected .basis or .Bint)");
  fi;

  # K <= (C7)^7
  K := KernelFromSubspace_CpPower(7, 7, Bint);

  # H on blocks
  liftsH := LiftH_Block(recH, 7, 7);

  gens := ShallowCopy(GeneratorsOfGroup(K));
  Append(gens, liftsH);
  G := Group(gens);
  return G;
end;

#############################################################################
## 5. Counting utilities
#############################################################################

CountTG49_Subspaces := function()
  local total, recH;
  EnsureTG49_HSubspaces();
  total := 0;
  for recH in TG49_HSubspaces do
    total := total + Length(recH.subspaces);
  od;
  Print("Total subspace records in TG49_HSubspaces: ", total, "\n");
  return total;
end;

CountTG49_SubspacesByH := function()
  local recH, dims, sub, d;
  EnsureTG49_HSubspaces();

  for recH in TG49_HSubspaces do
    dims := rec();
    for sub in recH.subspaces do
      d := sub.dim;
      if not IsBound(dims.(String(d))) then
        dims.(String(d)) := 0;
      fi;
      dims.(String(d)) := dims.(String(d)) + 1;
    od;
    Print("H tid=", recH.tid, " |H|=", recH.size,
          "  #subspaces=", Length(recH.subspaces),
          "  dimsCount=", dims, "\n");
  od;
end;

#############################################################################
## 6. Enumerate groups
#############################################################################

# Returns list of groups (may contain duplicates up to equality/conjugacy).
EnumerateG49_FromAllSubspaces := function()
  local nloc, L, recH, sub, G, cnt, total;

  EnsureTG49_HSubspaces();
  nloc := 49;
  L := [];
  total := 0;

  for recH in TG49_HSubspaces do
    cnt := 0;
    for sub in recH.subspaces do
      G := G49_FromSubspaceRec(recH, sub);
      # By construction H is transitive on blocks and K is inside base;
      # but keep a cheap sanity check on degree.
      if DegreeOfGroup(G) = nloc then
        Add(L, G);
        cnt := cnt + 1;
      fi;
    od;
    total := total + cnt;
    Print("Built ", cnt, " groups for H tid=", recH.tid,
          " (|H|=", recH.size, ")\n");
  od;

  Print("TOTAL groups built: ", total, "\n");
  return L;
end;

# Returns list of records with metadata (recommended for later processing).
EnumerateG49_FromAllSubspaces_Info := function()
  local nloc, L, recH, sub, G, info;

  EnsureTG49_HSubspaces();
  nloc := 49;
  L := [];

  for recH in TG49_HSubspaces do
    for sub in recH.subspaces do
      G := G49_FromSubspaceRec(recH, sub);
      if DegreeOfGroup(G) <> nloc then
        continue;
      fi;
      info := rec(
        Hid   := recH.tid,
        Hsize := recH.size,
        subKey := sub.key,
        subDim := sub.dim,
        tag    := sub.tag,
        G      := G
      );
      Add(L, info);
    od;
  od;

  Print("TOTAL records built: ", Length(L), "\n");
  return L;
end;

#############################################################################
## 7. Notes on file size vs n=25
#############################################################################
##  - tg49_Hsubspaces.g stores only integer bases (and keys), not permutations.
##  - permutations are reconstructed deterministically here via the fixed
##    standard p-cycle a=(1..p) and block lifts, so the file stays small.
########################################################################
