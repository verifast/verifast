open Verifast2
open GMain

let show_ide initialPath prover =
  let path = ref None in
  let ctxts_lifo = ref None in
  let msg = ref None in
  let root = GWindow.window ~width:800 ~height:600 () in
  let actionGroup = GAction.action_group ~name:"Actions" () in
  let _ =
    let a = GAction.add_action in
    GAction.add_actions actionGroup [
      a "File" ~label:"_File";
      a "New" ~stock:`NEW;
      a "Open" ~stock:`OPEN;
      a "Save" ~stock:`SAVE ~accel:"<control>S";
      a "SaveAs" ~label:"Save _as";
      a "Verify" ~label:"_Verify";
      a "VerifyProgram" ~label:"Verify program" ~stock:`MEDIA_PLAY ~accel:"F5"
    ]
  in
  let ui = GAction.ui_manager() in
  ui#insert_action_group actionGroup 0;
  root#add_accel_group ui#get_accel_group;
  ui#add_ui_from_string "
    <ui>
      <menubar name='MenuBar'>
        <menu action='File'>
          <menuitem action='New' />
          <menuitem action='Open' />
          <menuitem action='Save' />
          <menuitem action='SaveAs' />
        </menu>
        <menu action='Verify'>
          <menuitem action='VerifyProgram' />
        </menu>
      </menubar>
      <toolbar name='ToolBar'>
        <toolitem action='Save' />
        <toolitem action='VerifyProgram' />
      </toolbar>
    </ui>
  ";
  let rootVbox = GPack.vbox ~packing:root#add () in
  rootVbox#pack (ui#get_widget "/MenuBar");
  let toolbar = new GButton.toolbar (GtkButton.Toolbar.cast (ui#get_widget "/ToolBar")#as_widget) in
  toolbar#set_icon_size `SMALL_TOOLBAR;
  toolbar#set_style `ICONS;
  rootVbox#pack (toolbar#coerce);
  let rootTable = GPack.paned `VERTICAL ~border_width:3 ~packing:(rootVbox#pack ~expand:true) () in
  let _ = rootTable#set_position 350 in
  let textPaned = GPack.paned `VERTICAL ~packing:(rootTable#pack1 ~resize:true ~shrink:true) () in
  textPaned#set_position 0;
  let srcPaned = GPack.paned `HORIZONTAL ~packing:(textPaned#pack2 ~resize:true ~shrink:true) () in
  srcPaned#set_position 500;
  let subPaned = GPack.paned `HORIZONTAL ~packing:(textPaned#pack1 ~resize:true ~shrink:true) () in
  subPaned#set_position 500;
  let textScroll = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN ~packing:(srcPaned#pack1 ~resize:true ~shrink:true) () in
  let srcText = GText.view ~packing:textScroll#add () in
  let buffer = srcText#buffer in
  let subScroll = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN ~packing:(subPaned#pack1 ~resize:true ~shrink:true) () in
  let subText = GText.view ~buffer:buffer ~packing:subScroll#add () in
  let _ = (new GObj.misc_ops srcText#as_widget)#modify_font_by_name "Courier 10" in
  let _ = (new GObj.misc_ops subText#as_widget)#modify_font_by_name "Courier 10" in
  let updateWindowTitle() =
    let part1 = (match !path with None -> "(New buffer)" | Some path -> path) ^ (if buffer#modified then " (Modified)" else "") in
    let part3 = match !msg with None -> "" | Some msg -> " - " ^ msg in
    root#set_title (part1 ^ " - VeriFast IDE" ^ part3)
  in
  let load newPath =
    try
      let chan = open_in newPath in
      let rec iter () =
        let buf = String.create 60000 in
        let result = input chan buf 0 60000 in
        if result = 0 then [] else (String.sub buf 0 result)::iter()
      in
      let chunks = iter() in
      let _ = close_in chan in
      buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter;
      let gIter = buffer#start_iter in
      List.iter (fun chunk -> buffer#insert ~iter:gIter chunk) chunks;
      buffer#set_modified false;
      path := Some newPath;
      updateWindowTitle()
    with Sys_error msg -> GToolbox.message_box "VeriFast IDE" ("Could not load file: " ^ msg)
  in
  (match initialPath with None -> () | Some path -> load path);
  let store thePath =
    path := Some thePath;
    let chan = open_out thePath in
    let gBuf = buffer in
    let text = gBuf#get_text () in
    output_string chan text;
    close_out chan;
    buffer#set_modified false;
    updateWindowTitle();
    Some thePath
  in
  let rec saveAs() =
    match GToolbox.select_file ~title:"Save" () with
      None -> None
    | Some thePath ->
      if Sys.file_exists thePath then
        match GToolbox.question_box ~title:"VeriFast" ~buttons:["Yes"; "No"; "Cancel"] "The file already exists. Overwrite?" with
          1 -> store thePath
        | 2 -> saveAs()
        | _ -> None
      else
        store thePath
  in
  let save() =
    match !path with
      None -> saveAs()
    | Some thePath ->
      store thePath
  in
  let bottomTable = GPack.paned `HORIZONTAL () in
  let bottomTable2 = GPack.paned `HORIZONTAL () in
  let _ = bottomTable#pack2 ~resize:true ~shrink:true (bottomTable2#coerce) in
  let _ = rootTable#pack2 ~resize:true ~shrink:true (bottomTable#coerce) in
  let create_steplistbox =
    let collist = new GTree.column_list in
    let col_k = collist#add Gobject.Data.int in
    let col_text = collist#add Gobject.Data.string in
    let store = GTree.tree_store collist in
    let scrollWin = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN () in
    let lb = GTree.view ~model:store ~packing:scrollWin#add () in
    lb#coerce#misc#modify_font_by_name "Sans 8";
    let col = GTree.view_column ~title:"Steps" ~renderer:(GTree.cell_renderer_text [], ["text", col_text]) () in
    let _ = lb#append_column col in
    (scrollWin, lb, col_k, col_text, col, store)
  in
  let create_listbox title =
    let collist = new GTree.column_list in
    let col_k = collist#add Gobject.Data.int in
    let col_text = collist#add Gobject.Data.string in
    let store = GTree.list_store collist in
    let scrollWin = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN () in
    let lb = GTree.view ~model:store ~packing:scrollWin#add () in
    lb#coerce#misc#modify_font_by_name "Sans 8";
    let col = GTree.view_column ~title:title ~renderer:(GTree.cell_renderer_text [], ["text", col_text]) () in
    let _ = lb#append_column col in
    (scrollWin, lb, col_k, col_text, col, store)
  in
  let (steplistFrame, stepList, stepKCol, stepCol, stepViewCol, stepStore) = create_steplistbox in
  let _ = bottomTable#pack1 ~resize:true ~shrink:true (steplistFrame#coerce) in
  let (assumptionsFrame, assumptionsList, assumptionsKCol, assumptionsCol, _, assumptionsStore) = create_listbox "Assumptions" in
  let _ = bottomTable2#pack1 ~resize:true ~shrink:true (assumptionsFrame#coerce) in
  let (chunksFrame, chunksList, chunksKCol, chunksCol, _, chunksStore) = create_listbox "Heap chunks" in
  let _ = bottomTable2#pack2 ~resize:true ~shrink:true (chunksFrame#coerce) in
  let (srcEnvFrame, srcEnvList, srcEnvKCol, srcEnvCol, _, srcEnvStore) = create_listbox "Locals" in
  let _ = srcPaned#pack2 ~resize:true ~shrink:true (srcEnvFrame#coerce) in
  let (subEnvFrame, subEnvList, subEnvKCol, subEnvCol, _, subEnvStore) = create_listbox "Locals" in
  let _ = subPaned#pack2 ~resize:true ~shrink:true (subEnvFrame#coerce) in
  let stepItems = ref None in
  let updateStepItems() =
    let ctxts_fifo = List.rev (match !ctxts_lifo with Some l -> l) in
    let rec iter k itstack last_it ass locstack last_loc last_env ctxts =
      match ctxts with
        [] -> []
      | Assuming t::cs -> iter k itstack last_it (t::ass) locstack last_loc last_env cs
      | Executing (h, env, l, msg)::cs ->
        let it = stepStore#append ?parent:(match itstack with [] -> None | it::_ -> Some it) () in
        stepStore#set ~row:it ~column:stepKCol k;
        stepStore#set ~row:it ~column:stepCol msg;
        (ass, h, env, l, msg, locstack)::iter (k + 1) itstack (Some it) ass locstack (Some l) (Some env) cs
      | PushSubcontext::cs ->
        (match (last_it, last_loc, last_env) with (Some it, Some l, Some env) -> iter k (it::itstack) None ass ((l, env)::locstack) None None cs)
      | PopSubcontext::cs ->
        (match (itstack, locstack) with (_::itstack, _::locstack) -> iter k itstack None ass locstack None None cs)
    in
    stepItems := Some (iter 0 [] None [] [] None None ctxts_fifo)
  in
  let append_items (store:GTree.list_store) kcol col items =
    let rec iter k items =
      match items with
        [] -> ()
      | item::items ->
        let gIter = store#append() in
        store#set ~row:gIter ~column:kcol k;
        store#set ~row:gIter ~column:col item;
        iter (k + 1) items
    in
    iter 0 items
  in
  let clearStepInfo() =
    buffer#remove_tag_by_name "currentLine" ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#remove_tag_by_name "currentCaller" ~start:buffer#start_iter ~stop:buffer#end_iter;
    assumptionsStore#clear();
    chunksStore#clear();
    srcEnvStore#clear();
    subEnvStore#clear()
  in
  let currentStepMark = buffer#create_mark (buffer#start_iter) in
  let currentCallerMark = buffer#create_mark (buffer#start_iter) in
  let srcpos_iter (_, line, col) = buffer#get_iter (`LINECHAR (line - 1, col - 1)) in
  let apply_tag_by_loc name (p1, p2) =
    buffer#apply_tag_by_name name ~start:(srcpos_iter p1) ~stop:(srcpos_iter p2)
  in
  let stepSelected _ =
    match !stepItems with
      None -> ()
    | Some stepItems ->
      clearStepInfo();
      let [selpath] = stepList#selection#get_selected_rows in
      let k = let gIter = stepStore#get_iter selpath in stepStore#get ~row:gIter ~column:stepKCol in
      let (ass, h, env, l, msg, locstack) = List.nth stepItems k in
      apply_tag_by_loc "currentLine" l;
      let (current_line_pos, _) = l in
      buffer#move_mark (`MARK currentStepMark) ~where:(srcpos_iter current_line_pos);
      begin
        match locstack with
          [] ->
          srcText#scroll_to_mark ~within_margin:0.2 (`MARK currentStepMark);
          append_items srcEnvStore srcEnvKCol srcEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups env))
        | (caller_loc, caller_env)::_ ->
          apply_tag_by_loc "currentCaller" caller_loc;
          let (current_caller_pos, _) = caller_loc in
          buffer#move_mark (`MARK currentCallerMark) ~where:(srcpos_iter current_caller_pos);
          (if textPaned#position < 10 then textPaned#set_position 100);
          subText#scroll_to_mark ~within_margin:0.2 (`MARK currentStepMark);
          srcText#scroll_to_mark ~within_margin:0.2 (`MARK currentCallerMark);
          append_items srcEnvStore srcEnvKCol srcEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups caller_env));
          append_items subEnvStore subEnvKCol subEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups env))
      end;
      let _ = append_items assumptionsStore assumptionsKCol assumptionsCol (List.rev ass) in
      let _ = append_items chunksStore chunksKCol chunksCol (List.map (fun (g, ts) -> g ^ "(" ^ String.concat ", " ts ^ ")") h) in
      ()
  in
  let _ = buffer#create_tag ~name:"keyword" [`WEIGHT `BOLD; `FOREGROUND "Blue"] in
  let _ = buffer#create_tag ~name:"ghostRange" [`BACKGROUND "#eeeeee"] in
  let _ = buffer#create_tag ~name:"error" [`UNDERLINE `DOUBLE; `FOREGROUND "Red"] in
  let _ = buffer#create_tag ~name:"currentLine" [`BACKGROUND "Yellow"] in
  let _ = buffer#create_tag ~name:"currentCaller" [`BACKGROUND "Green"] in
  let _ = stepList#connect#cursor_changed ~callback:stepSelected in
  let _ = updateWindowTitle() in
  let _ = (new GObj.misc_ops stepList#as_widget)#grab_focus() in
  let updateStepListView() =
    stepList#expand_all();
    let lastStepRowPath = stepStore#get_path (stepStore#iter_children ~nth:(stepStore#iter_n_children None - 1) None) in
    let _ = stepList#selection#select_path lastStepRowPath in
    stepList#scroll_to_cell lastStepRowPath stepViewCol;
    let (_, _, _, l, _, _) = match !stepItems with Some stepItems -> List.nth stepItems (List.length stepItems - 1) in
    apply_tag_by_loc "error" l
  in
  let ensureSaved() =
    if buffer#modified then
      match GToolbox.question_box ~title:"VeriFast" ~buttons:["Save"; "Discard"; "Cancel"] "There are unsaved changes." with
        1 -> (match save() with None -> true | Some _ -> false)
      | 2 -> false
      | _ -> true
    else
      false
  in
  let _ = root#connect#destroy ~callback:GMain.Main.quit in
  let _ = buffer#connect#modified_changed (fun () ->
    updateWindowTitle()
  ) in
  let clearTrace() =
    clearStepInfo();
    stepStore#clear();
    let gBuf = buffer in
    buffer#remove_tag_by_name "error" ~start:gBuf#start_iter ~stop:gBuf#end_iter
  in
  let _ = buffer#connect#changed (fun () ->
    msg := None;
    stepItems := None;
    updateWindowTitle();
    clearTrace()
  ) in
  let _ = root#event#connect#delete ~callback:(fun _ ->
    ensureSaved()
  ) in
  (actionGroup#get_action "New")#connect#activate (fun _ ->
    if not (ensureSaved()) then
    begin
      path := None;
      clearTrace();
      buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter;
      buffer#set_modified false;
      updateWindowTitle()
    end
  );
  (actionGroup#get_action "Open")#connect#activate (fun _ ->
    if not (ensureSaved()) then
    begin
      match GToolbox.select_file ~title:"Open" () with
        None -> ()
      | Some thePath ->
        load thePath
    end
  );
  (actionGroup#get_action "Save")#connect#activate (fun () -> save(); ());
  (actionGroup#get_action "SaveAs")#connect#activate (fun () -> saveAs(); ());
  let handleStaticError l emsg =
    apply_tag_by_loc "error" l;
    msg := Some emsg;
    updateWindowTitle();
    let (start, stop) = l in
    let it = srcpos_iter stop in
    buffer#place_cursor ~where:it;
    srcText#scroll_to_iter ~within_margin:0.2 it; (* NOTE: scoll_to_iter returns a boolean *)
    ()
  in
  let reportKeyword l =
    apply_tag_by_loc "keyword" l
  in
  let reportGhostRange l =
    apply_tag_by_loc "ghostRange" l
  in
  let verifyProgram() =
    clearTrace();
    buffer#remove_tag_by_name "keyword" ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#remove_tag_by_name "ghostRange" ~start:buffer#start_iter ~stop:buffer#end_iter;
    try
      verify_program None false false "(buffer)" (Stream.of_string (buffer#get_text())) reportKeyword reportGhostRange;
      msg := Some "0 errors found";
      updateWindowTitle()
    with
      ParseException (l, emsg) ->
      handleStaticError l ("Parse error" ^ (if emsg = "" then "." else ": " ^ emsg))
    | StaticError (l, emsg) ->
      handleStaticError l emsg
    | SymbolicExecutionError (ctxts, phi, l, emsg) ->
      ctxts_lifo := Some ctxts;
      msg := Some emsg;
      updateWindowTitle();
      updateStepItems();
      updateStepListView();
      stepSelected()
  in
  (actionGroup#get_action "VerifyProgram")#connect#activate verifyProgram;
  let _ = root#show() in
  (* This hack works around the problem that GText.text_view#scroll_to_mark does not seem to work if called before the GUI is running properly. *)
  Glib.Idle.add (fun () -> stepSelected(); false);
  GMain.main()

let _ =
  try
    match Sys.argv with
      [| _ |] -> show_ide None "z3"
    | [| _; path |] -> show_ide (Some path) "z3"
    | [| _; "-prover"; prover; path |] -> show_ide (Some path) prover
    | _ -> GToolbox.message_box "VeriFast IDE" "Invalid command line."
  with
    e -> GToolbox.message_box "VeriFast IDE" ("Exception during startup: " ^ Printexc.to_string e)
