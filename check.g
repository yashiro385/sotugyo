#############################################################################
# TG49_check_recs.g
# 使い方:
#   1) tg49_final_recs_by_size.g と同じディレクトリに置く
#   2) gap -q TG49_check_recs.g
#
# 入力ファイル名は変更しません（Read するだけで書き換えません）。
#############################################################################

TG49_DATAFILE := "tg49_final_recs_by_size.g";

# オプション
TG49_DO_SIZE_CHECK := true;        # Size(G) を rec.size と突き合わせる
TG49_PRINT_EVERY   := 200;         # 進捗表示間隔（0で無効）
TG49_ABORT_ON_ERR  := false;       # true なら最初の失敗で止める

Read(TG49_DATAFILE);

if not IsBound(bySize) then
  Error("Expected variable 'bySize' after reading ", TG49_DATAFILE, "\n");
fi;

TG49_CheckOne := function(bucket, r, iB, iR)
  local gens, G, moved, ok, reasons, expected, computed, mpmax, mplen;

  ok := true;
  reasons := [];

  if not IsRecord(bucket) or not IsBound(bucket.size) or not IsBound(bucket.recs) then
    return rec(ok:=false, reasons:=["malformed bucket record"], where:=Concatenation("bucket#", String(iB)));
  fi;

  if not IsRecord(r) or not IsBound(r.gen) then
    return rec(ok:=false, reasons:=["missing field 'gen'"], where:=Concatenation("bucket#", String(iB), " rec#", String(iR)));
  fi;

  gens := r.gen;

  # generator sanity (optional)
  if not IsList(gens) or Length(gens)=0 then
    ok := false; Add(reasons, "gen is not a nonempty list");
    return rec(ok:=ok, reasons:=reasons);
  fi;

  # build group
  G := Group(gens);

  # degree / moved points check (strict 1..49)
  moved := MovedPoints(G);
  mplen := Length(moved);
  

  if mplen = 0 then
    mpmax := 0;
  else
    mpmax := moved[mplen];
  fi;

  # 最も確実：MovedPoints がちょうど [1..49] か
  if moved <> [1..49] then
    ok := false;
    Add(reasons, Concatenation("MovedPoints(G) not exactly [1..49] (len=",
                               String(mplen), ", max=", String(mpmax), ")"));
  fi;

  # transitivity check (explicit)
  if not IsTransitive(G, [1..49]) then
    ok := false;
    Add(reasons, "IsTransitive(G,[1..49]) = false");
  fi;


  if not (mplen = 49 and moved[1] = 1 and mpmax = 49) then
    ok := false;
    Add(reasons, Concatenation("MovedPoints(G) not exactly [1..49] (len=", String(mplen), ", max=", String(mpmax), ")"));
  fi;

  # transitivity check (explicit)
  if not IsTransitive(G, [1..49]) then
    ok := false;
    Add(reasons, "IsTransitive(G,[1..49]) = false");
  fi;

  # size check
  if TG49_DO_SIZE_CHECK then
    expected := bucket.size;
    if IsBound(r.size) then
      if r.size <> expected then
        ok := false;
        Add(reasons, Concatenation("rec.size (", String(r.size), ") != bucket.size (", String(expected), ")"));
      fi;
      expected := r.size;
    fi;

    computed := Size(G);
    if computed <> expected then
      ok := false;
      Add(reasons, Concatenation("Size(G)=", String(computed), " != expected=", String(expected)));
    fi;
  fi;

  return rec(ok:=ok, reasons:=reasons);
end;

TG49_RunCheck := function()
  local total, bad, pass, iB, iR, bucket, r, res, lastSize, thisSize;

  total := 0; pass := 0;
  bad := [];

  lastSize := -1;
  for iB in [1..Length(bySize)] do
    bucket := bySize[iB];

    if IsRecord(bucket) and IsBound(bucket.size) then
      thisSize := bucket.size;
      if thisSize < lastSize then
        Add(bad, rec(where:=Concatenation("bucket#", String(iB)),
                     reasons:=[Concatenation("bucket sizes not nondecreasing: ", String(lastSize), " -> ", String(thisSize))]));
      fi;
      lastSize := thisSize;
    fi;

    if not IsRecord(bucket) or not IsBound(bucket.recs) then
      Add(bad, rec(where:=Concatenation("bucket#", String(iB)),
                   reasons:=["bucket has no field 'recs'"]));
      if TG49_ABORT_ON_ERR then break; fi;
      continue;
    fi;

    for iR in [1..Length(bucket.recs)] do
      r := bucket.recs[iR];
      total := total + 1;

      if TG49_PRINT_EVERY > 0 and total mod TG49_PRINT_EVERY = 0 then
        Print("...checked ", total, " groups\n");
      fi;

      res := TG49_CheckOne(bucket, r, iB, iR);
      if res.ok then
        pass := pass + 1;
      else
        Add(bad, rec(bucketIndex:=iB, recIndex:=iR, bucketSize:=bucket.size, reasons:=res.reasons));
        if TG49_ABORT_ON_ERR then
          Print("FAILED at bucket#", iB, " rec#", iR, " (bucketSize=", bucket.size, ")\n");
          Print("  reasons: ", res.reasons, "\n");
          return rec(total:=total, pass:=pass, bad:=bad);
        fi;
      fi;
    od;
  od;

  return rec(total:=total, pass:=pass, bad:=bad);
end;

res := TG49_RunCheck();

Print("\n===== TG49 CHECK SUMMARY =====\n");
Print("file: ", TG49_DATAFILE, "\n");
Print("checked: ", res.total, "\n");
Print("passed : ", res.pass, "\n");
Print("failed : ", Length(res.bad), "\n");

if Length(res.bad) > 0 then
  Print("\nFirst failures (up to 20):\n");
  for i in [1..Minimum(20, Length(res.bad))] do
    Print("  #", i, ": bucket#", res.bad[i].bucketIndex, " rec#", res.bad[i].recIndex,
          " (bucketSize=", res.bad[i].bucketSize, ")\n");
    Print("     reasons: ", res.bad[i].reasons, "\n");
  od;
fi;
cntT := 0; cntM := 0; cntS := 0;
for e in res.bad do
  if ForAny(e.reasons, s -> PositionSublist(s, "IsTransitive") <> fail) then cntT := cntT + 1; fi;
  if ForAny(e.reasons, s -> PositionSublist(s, "MovedPoints") <> fail) then cntM := cntM + 1; fi;
  if ForAny(e.reasons, s -> PositionSublist(s, "Size(G)") <> fail) then cntS := cntS + 1; fi;
od;
Print("fail(IsTransitive): ", cntT, "\n");
Print("fail(MovedPoints) : ", cntM, "\n");
Print("fail(Size)        : ", cntS, "\n");

# 必要なら res.bad をファイルに書きたい場合（任意・コメント解除）
PrintTo("tg49_check_failures.txt", res.bad);

#############################################################################
