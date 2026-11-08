open Printf

type point = {
  id : int;
  line : int;
  col : int;
  kind : string;
  mutable hits : int;
}

type module_stats = {
  file : string;
  points : point array;
}

type file_metrics = {
  pts_total : int;
  pts_cov : int;
  lines_total : int;
  lines_cov : int;
  branches_total : int;
  branches_cov : int;
  funs_total : int;
  funs_cov : int;
}

let string_contains needle str =
  let nlen = String.length needle in
  let slen = String.length str in
  let rec loop i =
    if i + nlen > slen then false
    else if String.sub str i nlen = needle then true
    else loop (i + 1)
  in
  loop 0

let is_excluded_file file =
  let base = Filename.basename file in
  base = "vf_cov_runtime.ml" || base = "ppx_vf_cov.ml" || base = "vf_cov_report.ml" ||
  base = "vf_mir.ml" || base = "vf_mir_decoder.ml" ||
  base = "stubs_ast.ml" || string_contains "java_frontend" file ||
  base = "annotation_type_checker.ml" || base = "ast_reader.ml" ||
  base = "communication.ml" || base = "general_ast.ml" ||
  base = "java_frontend.ml" || base = "java_frontend_bridge.ml" ||
  base = "misc.ml" || (base = "ast_translator.ml" && string_contains "java" file) ||
  base = "rust_fe.ml" ||
  (base = "frontend.ml" && string_contains "refinement_checker" file) ||
  (base = "main.ml" && string_contains "refinement_checker" file) ||
  base = "SExpressionEmitter.ml" || base = "ocaml_expr_of_ast.ml" || base = "rocq_of_ast.ml" || base = "stringifier.ml"

let rec mkdir_p path =
  if path = "" || path = "." || Sys.file_exists path then ()
  else begin
    mkdir_p (Filename.dirname path);
    try Unix.mkdir path 0o755 with _ -> ()
  end

let ensure_parent_dir file =
  let dir = Filename.dirname file in
  if dir <> "" && dir <> "." then mkdir_p dir

let parse_vfcov_file (modules_tbl : (string, module_stats) Hashtbl.t) filepath =
  let ic = open_in filepath in
  let current_mod = ref None in
  try
    while true do
      let raw_line = input_line ic in
      let line = String.trim raw_line in
      if line <> "" then begin
        if String.length line >= 7 && String.sub line 0 7 = "MODULE " then begin
          let rest = String.sub line 7 (String.length line - 7) in
          match String.rindex_opt rest ' ' with
          | Some last_space ->
            let file = String.sub rest 0 last_space in
            if is_excluded_file file then
              current_mod := None
            else begin
            let num_points = int_of_string (String.sub rest (last_space + 1) (String.length rest - last_space - 1)) in
            let m =
              match Hashtbl.find_opt modules_tbl file with
              | Some existing when Array.length existing.points = num_points ->
                existing
              | Some existing ->
                if Array.length existing.points < num_points then begin
                  let pts = Array.init num_points (fun i ->
                    if i < Array.length existing.points then existing.points.(i)
                    else { id = i; line = 0; col = 0; kind = ""; hits = 0 })
                  in
                  let data = { file; points = pts } in
                  Hashtbl.replace modules_tbl file data;
                  data
                end else
                  existing
              | None ->
                let pts = Array.init num_points (fun i ->
                  { id = i; line = 0; col = 0; kind = ""; hits = 0 })
                in
                let data = { file; points = pts } in
                Hashtbl.replace modules_tbl file data;
                data
            in
            current_mod := Some m
            end
          | None -> ()
        end else begin
          match !current_mod with
          | None -> ()
          | Some m ->
            let parts = String.split_on_char ' ' line in
            match parts with
            | [id_s; line_s; col_s; kind; hits_s] ->
              let pt_id = int_of_string id_s in
              let line_num = int_of_string line_s in
              let col_num = int_of_string col_s in
              let hits = int_of_string hits_s in
              if pt_id >= 0 && pt_id < Array.length m.points then begin
                let p = m.points.(pt_id) in
                p.hits <- p.hits + hits;
                if p.line = 0 then begin
                  let updated = { id = pt_id; line = line_num; col = col_num; kind; hits = p.hits } in
                  m.points.(pt_id) <- updated
                end
              end
            | _ -> ()
        end
      end
    done
  with End_of_file ->
    close_in ic

let format_pct cov tot =
  if tot = 0 then "100.0%"
  else sprintf "%5.1f%%" ((float_of_int cov *. 100.0) /. float_of_int tot)

let pct_float cov tot =
  if tot = 0 then 100.0
  else (float_of_int cov *. 100.0) /. float_of_int tot

let compute_metrics m =
  let line_hits : (int, int) Hashtbl.t = Hashtbl.create 32 in
  let pts_total = Array.length m.points in
  let pts_cov = ref 0 in
  let funs_total = ref 0 in
  let funs_cov = ref 0 in
  let branches_total = ref 0 in
  let branches_cov = ref 0 in

  Array.iter (fun p ->
    let is_cov = p.hits > 0 in
    if is_cov then incr pts_cov;
    if p.line > 0 then begin
      let cur = match Hashtbl.find_opt line_hits p.line with Some h -> h | None -> 0 in
      Hashtbl.replace line_hits p.line (max cur p.hits)
    end;
    if p.kind = "fun" then begin
      incr funs_total;
      if is_cov then incr funs_cov
    end else begin
      incr branches_total;
      if is_cov then incr branches_cov
    end
  ) m.points;

  let lines_total = Hashtbl.length line_hits in
  let lines_cov = Hashtbl.fold (fun _ hits acc -> if hits > 0 then acc + 1 else acc) line_hits 0 in
  {
    pts_total;
    pts_cov = !pts_cov;
    lines_total;
    lines_cov;
    branches_total = !branches_total;
    branches_cov = !branches_cov;
    funs_total = !funs_total;
    funs_cov = !funs_cov;
  }

let generate_summary_text (mod_list : module_stats list) =
  let b = Buffer.create 4096 in
  let p fmt = ksprintf (fun s -> Buffer.add_string b s; Buffer.add_char b '\n') fmt in

  let sep = String.make 112 '-' in
  let double_sep = String.make 112 '=' in
  p "%s" double_sep;
  p "%-42s %-18s %-18s %-18s %-12s"
    "File" "Lines" "Branches" "Functions" "Points";
  p "%s" sep;

  let tot_pts = ref 0 in
  let cov_pts = ref 0 in
  let tot_lines = ref 0 in
  let cov_lines = ref 0 in
  let tot_branches = ref 0 in
  let cov_branches = ref 0 in
  let tot_funs = ref 0 in
  let cov_funs = ref 0 in

  List.iter (fun m ->
    let met = compute_metrics m in
    tot_pts := !tot_pts + met.pts_total;
    cov_pts := !cov_pts + met.pts_cov;
    tot_lines := !tot_lines + met.lines_total;
    cov_lines := !cov_lines + met.lines_cov;
    tot_branches := !tot_branches + met.branches_total;
    cov_branches := !cov_branches + met.branches_cov;
    tot_funs := !tot_funs + met.funs_total;
    cov_funs := !cov_funs + met.funs_cov;

    let line_str = sprintf "%d/%d (%s)" met.lines_cov met.lines_total (format_pct met.lines_cov met.lines_total) in
    let br_str = sprintf "%d/%d (%s)" met.branches_cov met.branches_total (format_pct met.branches_cov met.branches_total) in
    let fun_str = sprintf "%d/%d (%s)" met.funs_cov met.funs_total (format_pct met.funs_cov met.funs_total) in
    let pt_str = sprintf "%d/%d" met.pts_cov met.pts_total in

    let display_file =
      if String.length m.file > 42 then "..." ^ String.sub m.file (String.length m.file - 39) 39
      else m.file
    in
    p "%-42s %-18s %-18s %-18s %-12s"
      display_file line_str br_str fun_str pt_str
  ) mod_list;

  p "%s" sep;
  let all_line_str = sprintf "%d/%d (%s)" !cov_lines !tot_lines (format_pct !cov_lines !tot_lines) in
  let all_br_str = sprintf "%d/%d (%s)" !cov_branches !tot_branches (format_pct !cov_branches !tot_branches) in
  let all_fun_str = sprintf "%d/%d (%s)" !cov_funs !tot_funs (format_pct !cov_funs !tot_funs) in
  let all_pt_str = sprintf "%d/%d" !cov_pts !tot_pts in
  p "%-42s %-18s %-18s %-18s %-12s"
    "OVERALL" all_line_str all_br_str all_fun_str all_pt_str;
  p "%s" double_sep;
  p "OCaml Coverage Summary:";
  p "  - Line Coverage:     %s (%d / %d lines)" (format_pct !cov_lines !tot_lines) !cov_lines !tot_lines;
  p "  - Branch Coverage:   %s (%d / %d branches)" (format_pct !cov_branches !tot_branches) !cov_branches !tot_branches;
  p "  - Function Coverage: %s (%d / %d functions)" (format_pct !cov_funs !tot_funs) !cov_funs !tot_funs;
  p "  - Total Points:      %s (%d / %d points)" (format_pct !cov_pts !tot_pts) !cov_pts !tot_pts;
  p "%s" double_sep;
  Buffer.contents b

let write_json (mod_list : module_stats list) out_file =
  ensure_parent_dir out_file;
  let oc = open_out out_file in
  let tot_pts = ref 0 in
  let cov_pts = ref 0 in
  let tot_lines = ref 0 in
  let cov_lines = ref 0 in
  let tot_branches = ref 0 in
  let cov_branches = ref 0 in
  let tot_funs = ref 0 in
  let cov_funs = ref 0 in

  let metrics_list = List.map (fun m -> (m, compute_metrics m)) mod_list in

  List.iter (fun (_, met) ->
    tot_pts := !tot_pts + met.pts_total;
    cov_pts := !cov_pts + met.pts_cov;
    tot_lines := !tot_lines + met.lines_total;
    cov_lines := !cov_lines + met.lines_cov;
    tot_branches := !tot_branches + met.branches_total;
    cov_branches := !cov_branches + met.branches_cov;
    tot_funs := !tot_funs + met.funs_total;
    cov_funs := !cov_funs + met.funs_cov
  ) metrics_list;

  let overall_pct = pct_float !cov_pts !tot_pts in
  let line_cov_pct = pct_float !cov_lines !tot_lines in
  let branch_cov_pct = pct_float !cov_branches !tot_branches in
  let fun_cov_pct = pct_float !cov_funs !tot_funs in

  fprintf oc "{\n";
  fprintf oc "  \"total_points\": %d,\n" !tot_pts;
  fprintf oc "  \"covered_points\": %d,\n" !cov_pts;
  fprintf oc "  \"coverage_pct\": %.2f,\n" overall_pct;
  fprintf oc "  \"lines_total\": %d,\n" !tot_lines;
  fprintf oc "  \"lines_covered\": %d,\n" !cov_lines;
  fprintf oc "  \"line_coverage_pct\": %.2f,\n" line_cov_pct;
  fprintf oc "  \"branches_total\": %d,\n" !tot_branches;
  fprintf oc "  \"branches_covered\": %d,\n" !cov_branches;
  fprintf oc "  \"branch_coverage_pct\": %.2f,\n" branch_cov_pct;
  fprintf oc "  \"functions_total\": %d,\n" !tot_funs;
  fprintf oc "  \"functions_covered\": %d,\n" !cov_funs;
  fprintf oc "  \"function_coverage_pct\": %.2f,\n" fun_cov_pct;
  fprintf oc "  \"files\": [\n";

  let first_file = ref true in
  List.iter (fun (m, met) ->
    if not !first_file then fprintf oc ",\n" else first_file := false;
    let file_pct = pct_float met.pts_cov met.pts_total in
    let file_line_pct = pct_float met.lines_cov met.lines_total in
    let file_br_pct = pct_float met.branches_cov met.branches_total in
    let file_fn_pct = pct_float met.funs_cov met.funs_total in

    fprintf oc "    {\n";
    fprintf oc "      \"file\": \"%s\",\n" (String.escaped m.file);
    fprintf oc "      \"total_points\": %d,\n" met.pts_total;
    fprintf oc "      \"covered_points\": %d,\n" met.pts_cov;
    fprintf oc "      \"coverage_pct\": %.2f,\n" file_pct;
    fprintf oc "      \"lines_total\": %d,\n" met.lines_total;
    fprintf oc "      \"lines_covered\": %d,\n" met.lines_cov;
    fprintf oc "      \"line_coverage_pct\": %.2f,\n" file_line_pct;
    fprintf oc "      \"branches_total\": %d,\n" met.branches_total;
    fprintf oc "      \"branches_covered\": %d,\n" met.branches_cov;
    fprintf oc "      \"branch_coverage_pct\": %.2f,\n" file_br_pct;
    fprintf oc "      \"functions_total\": %d,\n" met.funs_total;
    fprintf oc "      \"functions_covered\": %d,\n" met.funs_cov;
    fprintf oc "      \"function_coverage_pct\": %.2f,\n" file_fn_pct;
    fprintf oc "      \"points\": [\n";

    let num_pts = Array.length m.points in
    for i = 0 to num_pts - 1 do
      let p = m.points.(i) in
      if i > 0 then fprintf oc ",\n";
      fprintf oc "        {\"id\": %d, \"line\": %d, \"col\": %d, \"kind\": \"%s\", \"hits\": %d}"
        p.id p.line p.col (String.escaped p.kind) p.hits
    done;
    fprintf oc "\n      ]\n";
    fprintf oc "    }"
  ) metrics_list;

  fprintf oc "\n  ]\n}\n";
  close_out oc

let write_lcov (mod_list : module_stats list) out_file =
  ensure_parent_dir out_file;
  let oc = open_out out_file in
  List.iter (fun m ->
    fprintf oc "TN:\n";
    fprintf oc "SF:%s\n" m.file;

    let line_hits : (int, int) Hashtbl.t = Hashtbl.create 32 in
    let funs_total = ref 0 in
    let funs_cov = ref 0 in
    let branches_total = ref 0 in
    let branches_cov = ref 0 in

    Array.iter (fun p ->
      if p.line > 0 then begin
        let cur = match Hashtbl.find_opt line_hits p.line with Some h -> h | None -> 0 in
        Hashtbl.replace line_hits p.line (max cur p.hits)
      end;
      if p.kind = "fun" then begin
        incr funs_total;
        if p.hits > 0 then incr funs_cov;
        fprintf oc "FN:%d,fn_line_%d\n" p.line p.line;
        fprintf oc "FNDA:%d,fn_line_%d\n" p.hits p.line
      end else begin
        incr branches_total;
        if p.hits > 0 then incr branches_cov;
        let hits_str = if p.hits > 0 then string_of_int p.hits else "-" in
        fprintf oc "BRDA:%d,0,%d,%s\n" p.line p.id hits_str
      end
    ) m.points;

    fprintf oc "FNF:%d\n" !funs_total;
    fprintf oc "FNH:%d\n" !funs_cov;
    fprintf oc "BRF:%d\n" !branches_total;
    fprintf oc "BRH:%d\n" !branches_cov;

    let sorted_lines =
      Hashtbl.fold (fun line hits acc -> (line, hits) :: acc) line_hits []
      |> List.sort (fun (l1, _) (l2, _) -> compare l1 l2)
    in

    let lines_hit = ref 0 in
    List.iter (fun (line, hits) ->
      if hits > 0 then incr lines_hit;
      fprintf oc "DA:%d,%d\n" line hits
    ) sorted_lines;

    fprintf oc "LF:%d\n" (List.length sorted_lines);
    fprintf oc "LH:%d\n" !lines_hit;
    fprintf oc "end_of_record\n"
  ) mod_list;
  close_out oc

let write_uncovered_md (mod_list : module_stats list) out_file =
  ensure_parent_dir out_file;
  let oc = open_out out_file in
  let tot_pts = ref 0 in
  let cov_pts = ref 0 in
  let tot_lines = ref 0 in
  let cov_lines = ref 0 in
  let tot_br = ref 0 in
  let cov_br = ref 0 in

  List.iter (fun m ->
    let met = compute_metrics m in
    tot_pts := !tot_pts + met.pts_total;
    cov_pts := !cov_pts + met.pts_cov;
    tot_lines := !tot_lines + met.lines_total;
    cov_lines := !cov_lines + met.lines_cov;
    tot_br := !tot_br + met.branches_total;
    cov_br := !cov_br + met.branches_cov
  ) mod_list;

  let overall_pct = pct_float !cov_pts !tot_pts in
  let line_pct = pct_float !cov_lines !tot_lines in
  let br_pct = pct_float !cov_br !tot_br in

  fprintf oc "# Uncovered Branches and Expressions Report\n\n";
  fprintf oc "- **Line Coverage:** %.1f%% (%d / %d lines covered)\n" line_pct !cov_lines !tot_lines;
  fprintf oc "- **Branch Coverage:** %.1f%% (%d / %d branches covered)\n" br_pct !cov_br !tot_br;
  fprintf oc "- **Point Coverage:** %.1f%% (%d / %d points covered)\n" overall_pct !cov_pts !tot_pts;
  fprintf oc "- **Uncovered Points:** %d\n\n" (!tot_pts - !cov_pts);

  List.iter (fun m ->
    let num_pts = Array.length m.points in
    let uncov = ref [] in
    Array.iter (fun p ->
      if p.hits = 0 then uncov := p :: !uncov
    ) m.points;
    let uncov_pts = List.rev !uncov in
    let cov_count = num_pts - List.length uncov_pts in
    let file_pct = pct_float cov_count num_pts in

    if uncov_pts <> [] then begin
      fprintf oc "## `%s` (%.1f%% - %d/%d points covered)\n\n" m.file file_pct cov_count num_pts;
      fprintf oc "| Line | Col | Kind | Status |\n";
      fprintf oc "| :--- | :--- | :--- | :--- |\n";
      List.iter (fun p ->
        fprintf oc "| Line %d | Col %d | `%s` | 0 hits (uncovered) |\n" p.line p.col p.kind
      ) uncov_pts;
      fprintf oc "\n"
    end
  ) mod_list;
  close_out oc

let () =
  let cov_dir = ref "" in
  let out_json = ref "" in
  let out_lcov = ref "" in
  let out_md = ref "" in
  let out_txt = ref "" in

  let speclist = [
    ("--cov-dir", Arg.Set_string cov_dir, "Directory containing .vfcov raw coverage dumps");
    ("--out-json", Arg.Set_string out_json, "Path to output JSON summary");
    ("--out-lcov", Arg.Set_string out_lcov, "Path to output LCOV info tracefile");
    ("--out-md", Arg.Set_string out_md, "Path to output Markdown uncovered branches report");
    ("--out-txt", Arg.Set_string out_txt, "Path to output human-readable text summary table");
  ] in

  let usage = "Usage: vf_cov_report --cov-dir <dir> [--out-json <file>] [--out-lcov <file>] [--out-md <file>] [--out-txt <file>]" in
  Arg.parse speclist (fun _ -> ()) usage;

  if !cov_dir = "" then begin
    prerr_endline "Error: --cov-dir is required.";
    prerr_endline usage;
    exit 1
  end;

  let modules_tbl = Hashtbl.create 64 in

  if Sys.file_exists !cov_dir && Sys.is_directory !cov_dir then begin
    let files = Sys.readdir !cov_dir in
    Array.iter (fun f ->
      if Filename.check_suffix f ".vfcov" then begin
        let path = Filename.concat !cov_dir f in
        parse_vfcov_file modules_tbl path
      end
    ) files
  end else begin
    prerr_endline (sprintf "Warning: Coverage directory '%s' does not exist or is not a directory." !cov_dir)
  end;

  let mod_list =
    Hashtbl.fold (fun _ m acc -> m :: acc) modules_tbl []
    |> List.sort (fun m1 m2 -> String.compare m1.file m2.file)
  in

  let summary_text = generate_summary_text mod_list in
  print_string summary_text;

  let txt_target =
    if !out_txt <> "" then !out_txt
    else if !out_json <> "" then Filename.concat (Filename.dirname !out_json) "ocaml_coverage.txt"
    else ""
  in
  if txt_target <> "" then begin
    ensure_parent_dir txt_target;
    let oc = open_out txt_target in
    output_string oc summary_text;
    close_out oc
  end;

  if !out_json <> "" then write_json mod_list !out_json;
  if !out_lcov <> "" then write_lcov mod_list !out_lcov;
  if !out_md <> "" then write_uncovered_md mod_list !out_md
