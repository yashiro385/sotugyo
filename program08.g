#############################################################################
# tg49_finish_remaining9_fixed.g
#
# 49-spec wrapper:
#   - Calls TG49_Run_Fill123_C6(...) from saigo_invsubspaces49_fixed.g
#   - Saves results as rec(size:=..., gen:=[...])
#   - No TID / database usage.
#############################################################################

if not IsBoundGlobal("TG49_Run_Fill123_C6") then
  Read("saigo_invsubspaces49_fixed.g");;
fi;

TG49_Run_And_Save_Default := function(outFile)
  local opts, recs;

  opts := rec(
    do1 := true,
    do2 := true,
    do3 := true,
    doAllTopLifts := false,
    doDiagWithInv := true,
    # Submodule enumeration limits (raise maxDim to explore more, but slower)
    maxDim := 2,
    maxSub := fail,
    # record-level dedup via cheap hash
    dedup := true
  );

  recs := TG49_Run_Fill123_C6(opts);
  TG49_SaveRecs(outFile, recs);
  return recs;
end;

#############################################################################
# Example:
#   Read("saigo_invsubspaces49_fixed.g");;
#   Read("tg49_finish_remaining9_fixed.g");;
TG49_Run_And_Save_Default("tg49_recs_export_remain.g");;
#############################################################################
