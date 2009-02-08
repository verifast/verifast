open Verifast
open GMain

let show_ide initialPath prover =
  let ctxts_lifo = ref None in
  let msg = ref None in
  let appTitle = "Verifast " ^ Vfversion.version ^ " IDE" in
  let root = GWindow.window ~width:800 ~height:600 ~title:appTitle ~allow_shrink:true () in
  let actionGroup = GAction.action_group ~name:"Actions" () in
  let disableOverflowCheck = ref false in
  let _ =
    let a = GAction.add_action in
    GAction.add_actions actionGroup [
      a "File" ~label:"_File";
      a "New" ~stock:`NEW;
      a "Open" ~stock:`OPEN;
      a "Save" ~stock:`SAVE ~accel:"<control>S";
      a "SaveAs" ~label:"Save _as";
      a "Close" ~stock:`CLOSE;
      a "Verify" ~label:"_Verify";
      GAction.add_toggle_action "CheckOverflow" ~label:"Check arithmetic overflow" ~active:true ~callback:(fun toggleAction -> disableOverflowCheck := not toggleAction#get_active);
      a "VerifyProgram" ~label:"Verify program" ~stock:`MEDIA_PLAY ~accel:"F5";
      a "Help" ~label:"_Help";
      a "About" ~stock:`ABOUT ~callback:(fun _ -> GToolbox.message_box "VeriFast IDE" Verifast.banner)
    ]
  in
  let ui = GAction.ui_manager() in
  ui#insert_action_group actionGroup 0;
  root#add_accel_group ui#get_accel_group;
  ignore (ui#add_ui_from_string "
    <ui>
      <menubar name='MenuBar'>
        <menu action='File'>
          <menuitem action='New' />
          <menuitem action='Open' />
          <menuitem action='Save' />
          <menuitem action='SaveAs' />
          <menuitem action='Close' />
        </menu>
        <menu action='Verify'>
          <menuitem action='VerifyProgram' />
          <separator />
          <menuitem action='CheckOverflow' />
        </menu>
        <menu action='Help'>
          <menuitem action='About'/>
        </menu>
      </menubar>
      <toolbar name='ToolBar'>
        <toolitem action='Save' />
        <toolitem action='VerifyProgram' />
        <toolitem action='Close' />
      </toolbar>
    </ui>
  ");
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
  let textNotebook = GPack.notebook ~scrollable:true ~packing:(srcPaned#pack1 ~resize:true ~shrink:true) () in
  let subNotebook = GPack.notebook ~scrollable:true ~packing:(subPaned#pack1 ~resize:true ~shrink:true) () in
  let buffers = ref [] in
  let updateBufferTitle (path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) =
    let text = (match !path with None -> "(New buffer)" | Some path -> Filename.basename path) ^ (if buffer#modified then "*" else "") in
    textLabel#set_text text;
    subLabel#set_text text
  in
  let bufferChangeListener = ref (fun _ -> ()) in
  let current_tab = ref None in
  let add_buffer() =
    let path = ref None in
    let textLabel = GMisc.label ~text:"(untitled)" () in
    let textScroll =
      GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN
        ~packing:(fun widget -> ignore (textNotebook#append_page ~tab_label:textLabel#coerce widget)) () in
    let srcText = GText.view ~packing:textScroll#add () in
    let buffer = srcText#buffer in
    let _ = buffer#create_tag ~name:"keyword" [`WEIGHT `BOLD; `FOREGROUND "Blue"] in
    let _ = buffer#create_tag ~name:"ghostRange" [`BACKGROUND "#eeeeee"] in
    let _ = buffer#create_tag ~name:"error" [`UNDERLINE `DOUBLE; `FOREGROUND "Red"] in
    let _ = buffer#create_tag ~name:"currentLine" [`BACKGROUND "Yellow"] in
    let _ = buffer#create_tag ~name:"currentCaller" [`BACKGROUND "Green"] in
    let currentStepMark = buffer#create_mark (buffer#start_iter) in
    let currentCallerMark = buffer#create_mark (buffer#start_iter) in
    let subLabel = GMisc.label ~text:"(untitled)" () in
    let subScroll =
      GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN
        ~packing:(fun widget -> ignore (subNotebook#append_page ~tab_label:subLabel#coerce widget)) () in
    let subText = GText.view ~buffer:buffer ~packing:subScroll#add () in
    let _ = (new GObj.misc_ops srcText#as_widget)#modify_font_by_name "Courier 10" in
    let _ = (new GObj.misc_ops subText#as_widget)#modify_font_by_name "Courier 10" in
    let tab = (path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) in
    buffer#connect#modified_changed (fun () ->
      updateBufferTitle tab
    );
    buffer#connect#changed (fun () -> !bufferChangeListener tab);
    let focusIn _ = current_tab := Some tab; false in
    srcText#event#connect#focus_in ~callback:focusIn;
    subText#event#connect#focus_in ~callback:focusIn;
    buffers := !buffers @ [tab];
    tab
  in
  let updateWindowTitle() =
    let text = match !msg with None -> "" | Some msg -> " - " ^ msg in
    root#set_title (appTitle ^ text)
  in
  let load ((path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) newPath =
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
      List.iter (fun chunk -> (buffer: GText.buffer)#insert ~iter:gIter chunk) chunks;
      buffer#set_modified false;
      path := Some (Filename.concat (Filename.dirname newPath) (Filename.basename newPath));
      updateBufferTitle tab
    with Sys_error msg -> GToolbox.message_box "VeriFast IDE" ("Could not load file: " ^ msg)
  in
  begin
    let tab = add_buffer() in
    current_tab := Some tab;
    match initialPath with None -> () | Some path -> load tab path
  end;
  let store ((path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) thePath =
    path := Some thePath;
    let chan = open_out thePath in
    let gBuf = buffer in
    let text = (gBuf: GText.buffer)#get_text () in
    output_string chan text;
    close_out chan;
    buffer#set_modified false;
    updateBufferTitle tab;
    Some thePath
  in
  let rec saveAs tab =
    match GToolbox.select_file ~title:"Save" () with
      None -> None
    | Some thePath ->
      if Sys.file_exists thePath then
        match GToolbox.question_box ~title:"VeriFast" ~buttons:["Yes"; "No"; "Cancel"] "The file already exists. Overwrite?" with
          1 -> store tab thePath
        | 2 -> saveAs tab
        | _ -> None
      else
        store tab thePath
  in
  let save ((path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) =
    match !path with
      None -> saveAs tab
    | Some thePath ->
      store tab thePath
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
    List.iter (fun ((path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) ->
      buffer#remove_tag_by_name "currentLine" ~start:buffer#start_iter ~stop:buffer#end_iter;
      buffer#remove_tag_by_name "currentCaller" ~start:buffer#start_iter ~stop:buffer#end_iter
    ) !buffers;
    assumptionsStore#clear();
    chunksStore#clear();
    srcEnvStore#clear();
    subEnvStore#clear()
  in
  let tab_path (path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) = path in
  let tab_buffer (path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) = buffer in
  let tab_srcText (path, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) = srcText in
  let get_tab_for_path path0 =
    (* This function is called only at a time when no buffers are modified. *)
    let rec iter k tabs =
      match tabs with
        tab::tabs ->
        if !(tab_path tab) = Some path0 then (k, tab) else iter (k + 1) tabs
      | [] ->
        let tab = add_buffer() in load tab path0; (k, tab)
    in
    iter 0 !buffers
  in
  let srcpos_iter buffer (line, col) =
    buffer#get_iter (`LINECHAR (line - 1, col - 1))
  in
  let apply_tag_by_loc name ((p1, p2): loc) =
    let ((path1_base, path1_relpath) as path1, line1, col1) = p1 in
    let (path2, line2, col2) = p2 in
    assert (path1 = path2);
    let (_, tab) = get_tab_for_path (Filename.concat path1_base path1_relpath) in
    let buffer = tab_buffer tab in
    buffer#apply_tag_by_name name ~start:(srcpos_iter buffer (line1, col1)) ~stop:(srcpos_iter buffer (line2, col2))
  in
  let get_step_of_path selpath =
    let stepItems = match !stepItems with Some stepItems -> stepItems | None -> assert false in
    let k = let gIter = stepStore#get_iter selpath in stepStore#get ~row:gIter ~column:stepKCol in
    List.nth stepItems k
  in
  let stepSelected _ =
    match !stepItems with
      None -> ()
    | Some stepItems ->
      clearStepInfo();
      let [selpath] = stepList#selection#get_selected_rows in
      let (ass, h, env, l, msg, locstack) = get_step_of_path selpath in
      begin
        match locstack with
          [] ->
          apply_tag_by_loc "currentLine" l;
          let ((path, line, col), _) = l in
          let (k, (_, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark)) = get_tab_for_path (string_of_path path) in
          textNotebook#goto_page k;
          buffer#move_mark (`MARK currentStepMark) ~where:(srcpos_iter buffer (line, col));
          srcText#scroll_to_mark ~within_margin:0.2 (`MARK currentStepMark);
          append_items srcEnvStore srcEnvKCol srcEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups env))
        | (caller_loc, caller_env)::_ ->
          begin
            if textPaned#position < 10 then textPaned#set_position 150;
            apply_tag_by_loc "currentLine" l;
            let ((path, line, col), _) = l in
            let (k, (_, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark)) = get_tab_for_path (string_of_path path) in
            subNotebook#goto_page k;
            buffer#move_mark (`MARK currentStepMark) ~where:(srcpos_iter buffer (line, col));
            Glib.Idle.add (fun () -> subText#scroll_to_mark ~within_margin:0.2 (`MARK currentStepMark); false); 
            append_items subEnvStore subEnvKCol subEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups env))
          end;
          begin
            apply_tag_by_loc "currentCaller" caller_loc;
            let ((path, line, col), _) = caller_loc in
            let (k, (_, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark)) = get_tab_for_path (string_of_path path) in
            textNotebook#goto_page k;
            buffer#move_mark (`MARK currentCallerMark) ~where:(srcpos_iter buffer (line, col));
            srcText#scroll_to_mark ~within_margin:0.2 (`MARK currentCallerMark);
            append_items srcEnvStore srcEnvKCol srcEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups caller_env))
          end
      end;
      let _ = append_items assumptionsStore assumptionsKCol assumptionsCol (List.rev ass) in
      let _ = append_items chunksStore chunksKCol chunksCol (List.map Verifast.string_of_chunk h) in
      ()
  in
  let _ = stepList#connect#cursor_changed ~callback:stepSelected in
  let _ = updateWindowTitle() in
  let _ = (new GObj.misc_ops stepList#as_widget)#grab_focus() in
  let get_last_step_path() =
    let lastBigStep = stepStore#iter_children ~nth:(stepStore#iter_n_children None - 1) None in
    let lastBigStepChildCount = stepStore#iter_n_children (Some lastBigStep) in
    let lastStep = if lastBigStepChildCount > 0 then stepStore#iter_children ~nth:(lastBigStepChildCount - 1) (Some lastBigStep) else lastBigStep in
    stepStore#get_path lastStep
  in
  let updateStepListView() =
    stepList#expand_all();
    let lastStepRowPath = get_last_step_path() in
    let _ = stepList#selection#select_path lastStepRowPath in
    Glib.Idle.add (fun () -> stepList#scroll_to_cell lastStepRowPath stepViewCol; false)
  in
  let ensureSaved tab =
    if (tab_buffer tab)#modified then
      match GToolbox.question_box ~title:"VeriFast" ~buttons:["Save"; "Discard"; "Cancel"] "There are unsaved changes." with
        1 -> (match save tab with None -> true | Some _ -> false)
      | 2 -> false
      | _ -> true
    else
      false
  in
  let _ = root#connect#destroy ~callback:GMain.Main.quit in
  let clearTrace() =
    clearStepInfo();
    stepStore#clear();
    List.iter (fun tab ->
      let buffer = tab_buffer tab in
      buffer#remove_tag_by_name "error" ~start:buffer#start_iter ~stop:buffer#end_iter
    ) !buffers
  in
  bufferChangeListener := (fun tab ->
    if !msg <> None then
    begin
      msg := None;
      stepItems := None;
      updateWindowTitle();
      clearTrace()
    end
  );
  let _ = root#event#connect#delete ~callback:(fun _ ->
    let rec iter tabs =
      match tabs with
        [] -> false
      | tab::tabs -> ensureSaved tab || iter tabs
    in
    iter !buffers
  ) in
  (actionGroup#get_action "New")#connect#activate (fun _ ->
    ignore (add_buffer())
  );
  (actionGroup#get_action "Open")#connect#activate (fun _ ->
    match GToolbox.select_file ~title:"Open" () with
      None -> ()
    | Some thePath ->
      let tab = add_buffer() in
      load tab thePath
  );
  let get_current_tab() =
    match !current_tab with
      Some tab -> Some tab
    | None -> GToolbox.message_box "VeriFast IDE" ("Please select a buffer."); None
  in
  let close ((_, buffer, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) =
    if not (ensureSaved tab) then
    begin
      textNotebook#remove textScroll#coerce;
      subNotebook#remove subScroll#coerce;
      buffers := List.filter (fun tab0 -> not (tab0 == tab)) !buffers;
      match !current_tab with None -> () | Some tab0 -> if tab == tab0 then current_tab := None
    end
  in
  (actionGroup#get_action "Save")#connect#activate (fun () -> match get_current_tab() with Some tab -> save tab; () | None -> ());
  (actionGroup#get_action "SaveAs")#connect#activate (fun () -> match get_current_tab() with Some tab -> saveAs tab; () | None -> ());
  (actionGroup#get_action "Close")#connect#activate (fun () -> match get_current_tab() with Some tab -> close tab; () | None -> ());
  let handleStaticError l emsg =
    apply_tag_by_loc "error" l;
    msg := Some emsg;
    updateWindowTitle();
    let (start, stop) = l in
    let (path, line, col) = stop in
    let (k, tab) = get_tab_for_path (string_of_path path) in
    textNotebook#goto_page k;
    let buffer = tab_buffer tab in
    let it = srcpos_iter buffer (line, col) in
    buffer#place_cursor ~where:it;
    Glib.Idle.add (fun () -> (tab_srcText tab)#scroll_to_iter ~within_margin:0.2 it; (* NOTE: scoll_to_iter returns a boolean *) false);
    ()
  in
  let loc_path ((path, _, _), _) = path in
  let reportKeyword l =
    apply_tag_by_loc "keyword" l
  in
  let reportGhostRange l =
    apply_tag_by_loc "ghostRange" l
  in
  let ensureHasPath tab =
    match !(tab_path tab) with
      None -> save tab
    | Some path ->
      if (tab_buffer tab)#modified then store tab path else Some path
  in
  let verifyProgram() =
    clearTrace();
    List.iter (fun tab ->
      let buffer = tab_buffer tab in
      buffer#remove_tag_by_name "keyword" ~start:buffer#start_iter ~stop:buffer#end_iter;
      buffer#remove_tag_by_name "ghostRange" ~start:buffer#start_iter ~stop:buffer#end_iter
    ) !buffers;
    match get_current_tab() with
      None -> ()
    | Some tab ->
      begin
        match ensureHasPath tab with
          None -> ()
        | Some path ->
          begin
            let streamSource path = Stream.of_string (readFile path) in
            try
              let options = {option_verbose = false; option_disable_overflow_check = !disableOverflowCheck} in
              verify_program None false options path (Stream.of_string ((tab_buffer tab)#get_text())) streamSource reportKeyword reportGhostRange;
              msg := Some "0 errors found";
              updateWindowTitle()
            with
              ParseException (l, emsg) ->
              handleStaticError l ("Parse error" ^ (if emsg = "" then "." else ": " ^ emsg))
            | StaticError (l, emsg) ->
              handleStaticError l emsg
            | SymbolicExecutionError (ctxts, phi, l, emsg) ->
              ctxts_lifo := Some ctxts;
              updateStepItems();
              updateStepListView();
              stepSelected();
              let (ass, h, env, steploc, stepmsg, locstack) = get_step_of_path (get_last_step_path()) in
              if l = steploc then
              begin
                apply_tag_by_loc "error" l;
                msg := Some emsg;
                updateWindowTitle()
              end
              else
                handleStaticError l emsg
          end
      end
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
