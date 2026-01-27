#############################################################################
# tg49_size_dedup_export.g
#
# Reads the 4 provided files (supports their record formats), builds
# rec(size:=..., gen:=[...]) for each group, groups by size, and removes
# duplicate gens within each size (generator order ignored; identity () ignored).
#
# Supported input list variables (as seen in your 4 files):
#   - recs             := [ rec(size:=..., gen:=[...]), ... ];
#   - TG49_Candidates  := [ rec(sizeG:=..., gens:=[...]), ... ];
#   - TG49_REPS        := [ rec(gens:="perm ; perm ; ...", ...), ... ];
#
# Output file defines:
#   bySize := [ rec(size:=S, recs:=[ rec(size:=S, gen:=[...]), ... ]), ... ];
#   recs   := [ rec(size:=..., gen:=[...]), ... ];  # flattened, size-sorted
#############################################################################

#############################################################################
# String helpers
#############################################################################
TG49_Trim := function(str)
  local i, j, ws, n;
  ws := " \t\r\n";
  n := Length(str);
  i := 1;
  while i <= n and str[i] in ws do i := i + 1; od;
  j := n;
  while j >= i and str[j] in ws do j := j - 1; od;
  if j < i then return ""; fi;
  return str{[i..j]};
end;

TG49_SplitByChar := function(s, ch)
  local out, cur, i, c;
  out := []; cur := [];
  for i in [1..Length(s)] do
    c := s[i];
    if c = ch then
      Add(out, String(cur));
      cur := [];
    else
      Add(cur, c);
    fi;
  od;
  Add(out, String(cur));
  return out;
end;

TG49_JoinStrings := function(L, sep)
  local i, out;
  if Length(L) = 0 then return ""; fi;
  out := L[1];
  for i in [2..Length(L)] do
    out := Concatenation(out, sep, L[i]);
  od;
  return out;
end;

#############################################################################
# Parse "perm ; perm ; ..." to a list of permutations
#############################################################################
TG49_ParseGensString := function(s)
  local parts, p, gens;
  parts := TG49_SplitByChar(s, ';');
  gens := [];
  for p in parts do
    p := TG49_Trim(p);
    if p <> "" then
      Add(gens, EvalString(p));
    fi;
  od;
  return gens;
end;

#############################################################################
# Key for dedup: order-insensitive, ignores identity ()
#############################################################################
TG49_GensKey := function(gens)
  local ss;
  if IsPerm(gens) then
    gens := [ gens ];
  fi;
  if not IsList(gens) then
    return fail;
  fi;
  ss := List(gens, g -> String(g));
  ss := Filtered(ss, t -> t <> "()");
  ss := ShallowCopy(ss);
  Sort(ss);
  return TG49_JoinStrings(ss, "|");
end;

#############################################################################
# Load list variable from a file
#############################################################################
TG49_ResetLoadedVars := function()
  if IsBound(recs) then Unbind(recs); fi;
  if IsBound(TG49_Candidates) then Unbind(TG49_Candidates); fi;
  if IsBound(TG49_REPS) then Unbind(TG49_REPS); fi;
  if IsBound(tg49_reps) then Unbind(tg49_reps); fi;
end;

TG49_LoadListFromFile := function(f)
  TG49_ResetLoadedVars();
  Read(f);

  if IsBound(recs) and IsList(recs) then return recs; fi;
  if IsBound(TG49_Candidates) and IsList(TG49_Candidates) then return TG49_Candidates; fi;
  if IsBound(TG49_REPS) and IsList(TG49_REPS) then return TG49_REPS; fi;
  if IsBound(tg49_reps) and IsList(tg49_reps) then return tg49_reps; fi;

  Error(Concatenation("No supported list variable found in: ", f));
end;

#############################################################################
# Extract a unified (gen,size,key) from one record
#############################################################################
TG49_Extract := function(r)
  local gens, size, key;

  if not IsRecord(r) then return fail; fi;

  gens := fail;
  size := fail;

  # A: rec(size:=..., gen:=[...])
  if IsBound(r.gen) then
    if IsList(r.gen) or IsPerm(r.gen) then
      gens := r.gen;
      if IsBound(r.size) then size := r.size; fi;
    fi;

  # B: rec(sizeG:=..., gens:=[...])
  elif IsBound(r.gens) and (IsList(r.gens) or IsPerm(r.gens)) then
    gens := r.gens;
    if IsBound(r.sizeG) then size := r.sizeG; fi;

  # C: rec(gens:="... ; ...")
  elif IsBound(r.gens) and IsString(r.gens) then
    gens := TG49_ParseGensString(r.gens);

  # D: rec(rep:="... ; ...")
  elif IsBound(r.rep) and IsString(r.rep) then
    gens := TG49_ParseGensString(r.rep);
    if IsBound(r.size) then size := r.size; fi;
  fi;

  if gens = fail then return fail; fi;

  # Normalize gens to a list
  if IsPerm(gens) then gens := [ gens ]; fi;
  if not IsList(gens) then return fail; fi;

  # Sanity: only keep lists of permutations
  if not ForAll(gens, IsPerm) then
    return fail;
  fi;

  key := TG49_GensKey(gens);
  if key = fail then return fail; fi;

  return rec(gen := gens, size := size, key := key);
end;

#############################################################################
# Build + dedup within size, then export
#############################################################################
TG49_Build_Size_Dedup := function(files, outFile)
  local buckets, seenBySize, f, L, r, e, key, size, s,
        outBySize, sizes, blk, kept, flat, i, j, ff;

  buckets := rec();     # buckets.(String(size)) := [ rec(size:=..., gen:=...), ... ]
  seenBySize := rec();  # seenBySize.(String(size)) := set of keys

  for f in files do
    L := TG49_LoadListFromFile(f);
    for r in L do
      e := TG49_Extract(r);
      if e = fail then
        continue;
      fi;

      key := e.key;

      if e.size <> fail then
        size := e.size;
      else
        # If generators are empty (shouldn't happen), skip
        if Length(e.gen) = 0 then
          continue;
        fi;
        size := Size(Group(e.gen));
      fi;

      s := String(size);
      if not IsBound(buckets.(s)) then
        buckets.(s) := [];
        seenBySize.(s) := [];
      fi;

      # membership test on a set: PositionSet is fast
      if PositionSet(seenBySize.(s), key) = fail then
        AddSet(seenBySize.(s), key);
        Add(buckets.(s), rec(size := size, gen := e.gen));
      fi;
    od;
  od;

  # buckets -> sorted list
  sizes := ShallowCopy(RecNames(buckets));
  Sort(sizes, function(a,b) return Int(a) < Int(b); end);

  outBySize := [];
  flat := [];
  for s in sizes do
    kept := ShallowCopy(buckets.(s));
    Sort(kept, function(a,b) return TG49_GensKey(a.gen) < TG49_GensKey(b.gen); end);
    Add(outBySize, rec(size := Int(s), recs := kept));
    for i in [1..Length(kept)] do
      Add(flat, kept[i]);
    od;
  od;

  if outFile <> fail then
    ff := OutputTextFile(outFile, false);
    SetPrintFormattingStatus(ff, false);

    AppendTo(ff, "bySize := [\n");
    for i in [1..Length(outBySize)] do
      blk := outBySize[i];
      AppendTo(ff, "  rec(size:=", String(blk.size), ", recs:=[\n");
      for j in [1..Length(blk.recs)] do
        AppendTo(ff, "    rec(size:=", String(blk.recs[j].size), ", gen:=", String(blk.recs[j].gen), ")");
        if j < Length(blk.recs) then AppendTo(ff, ",\n"); else AppendTo(ff, "\n"); fi;
      od;
      AppendTo(ff, "  ])");
      if i < Length(outBySize) then AppendTo(ff, ",\n"); else AppendTo(ff, "\n"); fi;
    od;
    AppendTo(ff, "];\n\n");

    AppendTo(ff, "recs := [\n");
    for i in [1..Length(flat)] do
      AppendTo(ff, "  rec(size:=", String(flat[i].size), ", gen:=", String(flat[i].gen), ")");
      if i < Length(flat) then AppendTo(ff, ",\n"); else AppendTo(ff, "\n"); fi;
    od;
    AppendTo(ff, "];\n");

    CloseStream(ff);
  fi;

  return rec(bySize := outBySize, recs := flat);
end;

#############################################################################
# Convenience runner for your 4 files
#############################################################################
TG49_Run_4Files := function(outFile)
  return TG49_Build_Size_Dedup(
    [ "tg49_out.g",
      "tg49_recs_export_remain.g",
      "tg49_sylow_recs.g",
      "tg49_reps.g" ],
    outFile
  );
end;
res := TG49_Run_4Files("tg49_final_recs_by_size.g");

#############################################################################
# Usage:
#   Read("/mnt/data/tg49_size_dedup_export.g");
#   res := TG49_Run_4Files("/mnt/data/tg49_final_recs_by_size.g");
#   Length(res.recs);
#############################################################################
