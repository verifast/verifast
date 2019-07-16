let () =
  let app = GWindow.window () in
  let branchLeft = GdkPixbuf.from_file "../branch-left.png" in
  let branchRight = GdkPixbuf.from_file "../branch-right.png" in
  let table = GLineMarks.table () in
  let buffer = GSourceView2.source_buffer () in
  let addLineMark line column pixbuf =
    let iter = buffer#get_iter_at_char ~line column in
    let mark = buffer#create_mark iter in
    table#add mark pixbuf
  in
  let view = GSourceView2.source_view ~source_buffer:buffer () in
  buffer#set_text "Line 1.\nLine 2 (left branch)\nLine 3 (left branch and right branch)\nLine 4";
  addLineMark 2 24 branchRight;
  addLineMark 1 8 branchLeft;
  addLineMark 2 8 branchLeft;
  table#show_in_source_view view;
  let column = GLineMarks.source_gutter_text_column "99x" 1.0 in
  for i = 1 to 10 do
    column#add_line (Printf.sprintf "%2dx" i)
  done;
  column#show_in_source_view view;
  let scrolledWindow = GBin.scrolled_window () in
  scrolledWindow#add view#coerce;
  let rootVbox = GPack.vbox ~packing:app#add () in
  let openButton = GButton.button ~label:"Open" ~packing:(rootVbox#pack) () in
  openButton#connect#clicked (fun () -> ignore @@ GToolbox.select_file ~title:"Open" ());
  rootVbox#pack ~expand:true scrolledWindow#coerce;
  
  app#connect#destroy (fun () -> GMain.Main.quit ());
  app#show ();
  GMain.Main.main ()

