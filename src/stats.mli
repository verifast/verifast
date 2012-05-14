val parsing_stopwatch : Stopwatch.t
class stats :
  object
    val mutable branchCount : int
    val mutable closeParsedCount : int
    val mutable definitelyEqualQueryCount : int
    val mutable definitelyEqualSameTermCount : int
    val mutable execStepCount : int
    val mutable functionTimings : (string * float) list
    val mutable openParsedCount : int
    val mutable overhead :
      < ghost_lines : int; mixed_lines : int; nonghost_lines : int;
        path : string >
      list
    val mutable proverAssumeCount : int
    val mutable proverOtherQueryCount : int
    val mutable proverStats : string
    val startTicks : int64
    val startTime : float
    val mutable stmtExecCount : int
    val mutable stmtsParsedCount : int
    method appendProverStats : string * (string * int64) list -> unit
    method branch : unit
    method closeParsed : unit
    method definitelyEqualQuery : unit
    method definitelyEqualSameTerm : unit
    method execStep : unit
    method getFunctionTimings : string
    method openParsed : unit
    method overhead :
      path:string * string ->
      nonGhostLineCount:int ->
      ghostLineCount:int -> mixedLineCount:int -> unit
    method printStats : unit
    method proverAssume : unit
    method proverOtherQuery : unit
    method recordFunctionTiming : string -> float -> unit
    method stmtExec : unit
    method stmtParsed : unit
    method tickLength : float
  end
val stats : stats
