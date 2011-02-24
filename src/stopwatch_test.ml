let () =
  Stopwatch.lock_process_to_processor_1 ();
  let t0 = Sys.time () in
  let s = Stopwatch.create () in
  let s1 = Stopwatch.create () in
  Stopwatch.start s;
  let n = 1000000000 in
  for i = 1 to n do
    Stopwatch.start s1
  done;
  Stopwatch.stop s;
  let t1 = Sys.time () in
  let dt = t1 -. t0 in
  let ticks = Int64.to_float (Stopwatch.ticks s) in
  let tick_length = dt /. ticks in
  Printf.printf "Number of ticks elapsed: %f\n" ticks;
  Printf.printf "Time elapsed: %f seconds\n" dt;
  Printf.printf "Time per tick: %f nanoseconds\n" (tick_length *. 1.0e9);
  Printf.printf "Time per Stopwatch.start call: %f nanoseconds\n" (dt /. float_of_int n *. 1.0e9)