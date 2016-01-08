#load "unix.cma";;

open Unix;;
open Printf;;

let releases = [ (* Add new releases to the front *)
  "16.01", 1820;
  "15.12", 1807;
  "15.11", 1802;
  "15.05", 1738;
  "15.04", 1733;
  "14.12", 1694;
  "14.11", 1659;
  "14.10", 1640;
  "14.5", 1548;
  "13.11.14", 1467;
  "13.11", 1463;
  "12.12", 1307;
  "12.10", 1262;
  "12.9", 1247;
  "12.5.23", 1131;
  "12.5.23", 1130;
  "12.5", 1124;
  "12.3", 1058;
  "12.2", 1041;
  "11.12", 1016;
  "11.11.27", 1003;
  "11.11", 987;
  "11.9.19", 880;
  "11.9", 851;
  "10.6", 680;
  "10.5.2", 618;
  "10.5.1", 612;
  "10.5", 606;
  "10.4.1", 562;
  "10.4", 560;
  "10.3", 534;
  "10.2", 496;
  "10.1.1", 486;
  "10.1", 485;
  "10.0", 475;
  "9.2.1", 364;
  "9.2", 360;
  "9.0", 336;
  "8.1.2", 280;
  "8.1.1", 275
]

let string_of_process_status s =
  match s with
    WEXITED n -> Printf.sprintf "WEXITED %d" n
  | WSIGNALED n -> Printf.sprintf "WSIGNALED %d" n
  | WSTOPPED n -> Printf.sprintf "WSTOPPED %d" n

let sys cmd =
  let chan = Unix.open_process_in cmd in
  let line = input_line chan in
  let exitStatus = Unix.close_process_in chan in
  if exitStatus <> Unix.WEXITED 0 then failwith (Printf.sprintf "Command '%s' failed with exit status %s" cmd (string_of_process_status exitStatus));
  line

let is_macos = Sys.os_type = "Unix" && sys "uname" = "Darwin"
let is_64bit = Sys.word_size = 64

let sh ?(allow_fail = false) cmd =
  print_endline cmd;
  let result = Sys.command cmd in
  if result <> 0 && not allow_fail then failwith (Printf.sprintf "Command failed with exit code %d" result)

let rm_Rf_cmd = match Sys.os_type with "Win32" -> "rmdir /s /q " | _ -> "rm -Rf "
let rm_Rf dir = sh (rm_Rf_cmd ^ dir)

let (create_zip_cmd, zipext) =
  match Sys.os_type with
    "Win32" -> ("7z a", ".zip")
  | _ -> ("tar czf", ".tar.gz")

let create_zip zippath dirname = sh (Printf.sprintf "%s %s %s" create_zip_cmd zippath dirname)

let os_suffix = if is_macos then "-macos" else if is_64bit then "-x64" else ""

let (//) x y = Filename.concat x y

let () =
  try
  let (release, revision) =
    match List.tl (Array.to_list Sys.argv) with
      "--caller=build.ml"::args ->
      begin match args with
        [] -> List.hd releases
      | ["--release"; release] ->
        begin try
          (release, List.assoc release releases)
        with Not_found -> failwith (sprintf "No such release: '%s'" release)
        end
      | ["--revision"; revision] ->
        let revision =
          try
            int_of_string revision
          with Failure "int_of_string" -> failwith (sprintf "Revision must be a number: '%s'" revision)
        in
        (sprintf "r%d" revision, revision)
      | _ ->
        failwith begin
          "Command line syntax error.\n" ^
          "Usage:\n" ^
          "  build.ml [--release Release | --revision Revision]"
        end
      end
    | _ -> failwith "Please do not run this script directly; run build.ml instead."
  in
  let exportdir = ".." // "exportdir" in
  if Sys.file_exists exportdir then rm_Rf exportdir;
  sh (sprintf "svn export https://dnetcode.cs.kuleuven.be/svn/verifast/verifast/trunk@%d %s" revision exportdir);
  if Sys.file_exists "GNUmakefile.settings" then sh (sprintf "cp GNUmakefile.settings %s" exportdir);
  Sys.chdir exportdir;
  Sys.chdir "src";
  let mac_flag = if is_macos then "MAC=yes" else "" in
  sh (sprintf "make %s VFVERSION=%s release" mac_flag release);
  let releasename = Printf.sprintf "verifast-%s" release in
  let zipname = releasename ^ os_suffix ^ zipext in
  let zippath = ".." // ".." // zipname in
  if Sys.file_exists zippath then Sys.remove zippath;
  let zippath_tentative = zippath ^ "_tentative" in
  if Sys.file_exists zippath_tentative then Sys.remove zippath_tentative;
  create_zip zippath_tentative releasename;
  if is_macos then sh ~allow_fail:true "mv ~/gtk ~/gtk_";
  Sys.chdir releasename;
  print_endline "Please test the release. (Please test especially bin/vfide.)";
  sh "bash";
  Sys.chdir "..";
  if is_macos then sh ~allow_fail:true "mv ~/gtk_ ~/gtk";
  print_endline "Does the release work correctly? [yes/no]";
  let release_works = read_line () in
  if release_works <> "yes" then failwith "The release does not work.";
  sh (Printf.sprintf "mv %s %s" zippath_tentative zippath);
  Sys.chdir (".." // "..");
  sh (sprintf "%s %s" ("." // "upload") zipname)
  with
    Failure msg ->
      print_endline msg;
      exit 1
