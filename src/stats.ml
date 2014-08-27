open Util
open Ast

(* Region: Statistics *)

let parsing_stopwatch = Stopwatch.create ()

class stats =
  object (self)
    val startTime = Perf.time()
    val startTicks = Stopwatch.processor_ticks()
    val mutable stmtsParsedCount = 0
    val mutable openParsedCount = 0
    val mutable closeParsedCount = 0
    val mutable stmtExecOnAllPathsCount = 0
    val mutable stmtExecLocs = Hashtbl.create 1000;
    val mutable execStepCount = 0
    val mutable branchCount = 0
    val mutable proverAssumeCount = 0
    val mutable definitelyEqualSameTermCount = 0
    val mutable definitelyEqualQueryCount = 0
    val mutable proverOtherQueryCount = 0
    val mutable proverStats = ""
    val mutable overhead: <path: string; nonghost_lines: int; ghost_lines: int; mixed_lines: int> list = []
    val mutable functionTimings: (string * float) list = []
    
    method tickLength = let t1 = Perf.time() in let ticks1 = Stopwatch.processor_ticks() in (t1 -. startTime) /. Int64.to_float (Int64.sub ticks1 startTicks)

    method stmtParsed = stmtsParsedCount <- stmtsParsedCount + 1
    method openParsed = openParsedCount <- openParsedCount + 1
    method closeParsed = closeParsedCount <- closeParsedCount + 1
    method stmtExec (l: loc) =
      stmtExecOnAllPathsCount <- stmtExecOnAllPathsCount + 1;
      Hashtbl.replace stmtExecLocs l l
    method getStmtExec = Hashtbl.length stmtExecLocs
    method getStmtExecLocs = Hashtbl.fold (fun _ loc locs -> loc::locs) stmtExecLocs []
    method getStmtExecOnAllPaths = stmtExecOnAllPathsCount
    method execStep = execStepCount <- execStepCount + 1
    method branch = branchCount <- branchCount + 1
    method proverAssume = proverAssumeCount <- proverAssumeCount + 1
    method definitelyEqualSameTerm = definitelyEqualSameTermCount <- definitelyEqualSameTermCount + 1
    method definitelyEqualQuery = definitelyEqualQueryCount <- definitelyEqualQueryCount + 1
    method proverOtherQuery = proverOtherQueryCount <- proverOtherQueryCount + 1
    method appendProverStats (text, tickCounts) =
      let tickLength = self#tickLength in
      proverStats <- proverStats ^ text ^ String.concat "" (List.map (fun (lbl, ticks) -> Printf.sprintf "%s: %.6fs\n" lbl (Int64.to_float ticks *. tickLength)) tickCounts)
    method overhead ~path ~nonGhostLineCount ~ghostLineCount ~mixedLineCount =
      let (basepath, relpath) = path in
      let path = concat basepath relpath in
      let o = object method path = path method nonghost_lines = nonGhostLineCount method ghost_lines = ghostLineCount method mixed_lines = mixedLineCount end in
      overhead <- o::overhead
    method recordFunctionTiming funName seconds = if seconds > 0.1 then functionTimings <- (funName, seconds)::functionTimings
    method getFunctionTimings =
      let compare (_, t1) (_, t2) = compare t1 t2 in
      let timingsSorted = List.sort compare functionTimings in
      let max_funName_length = List.fold_left (fun m (n, _) -> max m (String.length n)) 0 timingsSorted in
      String.concat "" (List.map (fun (funName, seconds) -> Printf.sprintf "  %-*s: %6.2f seconds\n" max_funName_length funName seconds) timingsSorted)
    
    method printStats =
      print_endline ("Syntactic annotation overhead statistics:");
      let max_path_size = List.fold_left (fun m o -> max m (String.length o#path)) 0 overhead in
      List.iter
        begin fun o ->
          let overhead = float_of_int (o#ghost_lines + o#mixed_lines) *. 100.0 /. float_of_int o#nonghost_lines in
          Printf.printf "  %-*s: lines: code: %4d; annot: %4d; mixed: %4d; overhead: %4.0f%%\n"
            max_path_size o#path o#nonghost_lines o#ghost_lines o#mixed_lines overhead
        end
        overhead;
      print_endline ("Statements parsed: " ^ string_of_int stmtsParsedCount);
      print_endline ("Open statements parsed: " ^ string_of_int openParsedCount);
      print_endline ("Close statements parsed: " ^ string_of_int closeParsedCount);
      print_endline ("Statement executions: " ^ string_of_int (self#getStmtExec));
      print_endline ("Execution steps (including assertion production/consumption steps): " ^ string_of_int execStepCount);
      print_endline ("Symbolic execution forks: " ^ string_of_int branchCount);
      print_endline ("Prover assumes: " ^ string_of_int proverAssumeCount);
      print_endline ("Term equality tests -- same term: " ^ string_of_int definitelyEqualSameTermCount);
      print_endline ("Term equality tests -- prover query: " ^ string_of_int definitelyEqualQueryCount);
      print_endline ("Term equality tests -- total: " ^ string_of_int (definitelyEqualSameTermCount + definitelyEqualQueryCount));
      print_endline ("Other prover queries: " ^ string_of_int proverOtherQueryCount);
      print_endline ("Prover statistics:\n" ^ proverStats);
      Printf.printf "Time spent parsing: %.6fs\n" (Int64.to_float (Stopwatch.ticks parsing_stopwatch) *. self#tickLength);
      print_endline ("Function timings (> 0.1s):\n" ^ self#getFunctionTimings);
      print_endline (Printf.sprintf "Total time: %.2f seconds" (Perf.time() -. startTime))
  end

let stats = ref (new stats)

let clear_stats _ = 
  stats := (new stats)
  
