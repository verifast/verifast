open Verifast
open GMain

type undo_action =
  Insert of int * string
| Delete of int * string

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
      a "Save" ~stock:`SAVE ~accel:"<control>S" ~tooltip:"Save";
      a "SaveAs" ~label:"Save _as";
      a "Close" ~stock:`CLOSE ~tooltip:"Close";
      a "Edit" ~label:"_Edit";
      a "Undo" ~stock:`UNDO ~accel:"<Ctrl>Z";
      a "Redo" ~stock:`REDO ~accel:"<Ctrl>Y";
      a "Verify" ~label:"_Verify";
      GAction.add_toggle_action "CheckOverflow" ~label:"Check arithmetic overflow" ~active:true ~callback:(fun toggleAction -> disableOverflowCheck := not toggleAction#get_active);
      a "VerifyProgram" ~label:"Verify program" ~stock:`MEDIA_PLAY ~accel:"F5" ~tooltip:"Verify";
      a "RunToCursor" ~label:"_Run to cursor" ~stock:`JUMP_TO ~accel:"<Ctrl>F5" ~tooltip:"Run to cursor";
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
        <menu action='Edit'>
          <menuitem action='Undo' />
          <menuitem action='Redo' />
        </menu>
        <menu action='Verify'>
          <menuitem action='VerifyProgram' />
          <menuitem action='RunToCursor' />
          <separator />
          <menuitem action='CheckOverflow' />
        </menu>
        <menu action='Help'>
          <menuitem action='About'/>
        </menu>
      </menubar>
      <toolbar name='ToolBar'>
        <toolitem action='Save' />
        <toolitem action='Close' />
        <separator />
        <toolitem action='Undo' />
        <toolitem action='Redo' />
        <separator />
        <toolitem action='VerifyProgram' />
        <toolitem action='RunToCursor' />
      </toolbar>
    </ui>
  ");
  let undoAction = actionGroup#get_action "Undo" in
  let redoAction = actionGroup#get_action "Redo" in
  let ignore_text_changes = ref false in
  let rootVbox = GPack.vbox ~packing:root#add () in
  rootVbox#pack (ui#get_widget "/MenuBar");
  let toolbar = new GButton.toolbar (GtkButton.Toolbar.cast (ui#get_widget "/ToolBar")#as_widget) in
  toolbar#set_icon_size `SMALL_TOOLBAR;
  toolbar#set_style `ICONS;
  let separatorToolItem = GButton.separator_tool_item () in
  toolbar#insert separatorToolItem;
  let messageToolItem = GButton.tool_item ~expand:true () in
  messageToolItem#set_border_width 3;
  let messageEntry = GEdit.entry ~show:false ~editable:false ~has_frame:false ~packing:(messageToolItem#add) () in
  toolbar#insert messageToolItem;
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
  let updateBufferTitle (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) =
    let text = (match !path with None -> "(New buffer)" | Some path -> Filename.basename path) ^ (if buffer#modified then "*" else "") in
    textLabel#set_text text;
    subLabel#set_text text
  in
  let bufferChangeListener = ref (fun _ -> ()) in
  let current_tab = ref None in
  let set_current_tab tab =
    current_tab := tab;
    let (undoSensitive, redoSensitive) =
      match tab with
        None -> (false, false)
      | Some (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) ->
        (!undoList <> [], !redoList <> [])
    in
    undoAction#set_sensitive undoSensitive;
    redoAction#set_sensitive redoSensitive
  in
  let tag_name_of_range_kind kind =
    match kind with
      KeywordRange -> "keyword"
    | GhostKeywordRange -> "ghostKeyword"
    | GhostRange -> "ghostRange"
    | GhostRangeDelimiter -> "ghostRangeDelimiter"
    | CommentRange -> "comment"
    | ErrorRange -> "error"
  in
  let srcpos_iter buffer (line, col) =
    buffer#get_iter (`LINECHAR (line - 1, col - 1))
  in
  let string_of_iter it = string_of_int it#line ^ ":" ^ string_of_int it#line_offset in
  let rec perform_syntax_highlighting ((path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) start stop =
    let Some commentTag = GtkText.TagTable.lookup buffer#tag_table "comment" in
    let commentTag = new GText.tag commentTag in
    let Some ghostRangeTag = GtkText.TagTable.lookup buffer#tag_table "ghostRange" in
    let ghostRangeTag = new GText.tag ghostRangeTag in
    let start = start#backward_line in
    let stop = stop#forward_line in
    let startLine = start#line in
    let startIsInComment = start#has_tag commentTag && not (start#begins_tag (Some commentTag)) in
    let startIsInGhostRange = start#has_tag ghostRangeTag && not (start#begins_tag (Some ghostRangeTag)) in
    let stopIsInComment = stop#has_tag commentTag && not (stop#begins_tag (Some commentTag)) in
    let stopIsInGhostRange = stop#has_tag ghostRangeTag && not (start#begins_tag (Some ghostRangeTag)) in
    buffer#remove_all_tags ~start:start ~stop:stop;
    let reportRange kind ((_, line1, col1), (_, line2, col2)) =
      buffer#apply_tag_by_name (tag_name_of_range_kind kind) ~start:(srcpos_iter buffer (startLine + line1, col1)) ~stop:(srcpos_iter buffer (startLine + line2, col2))
    in
    let charStream =
      let iter = start#copy in
      let noCopyIter = iter#nocopy in
      Stream.from (fun offset ->
        if iter#equal stop then None else let c = char_of_int iter#char in noCopyIter#forward_char; Some c
      )
    in
    let highlight keywords =
      let (loc, ignore_eol, tokenStream, in_comment, in_ghost_range) =
        make_lexer_core keywords ("<bufferBase>", "<buffer>") charStream reportRange startIsInComment startIsInGhostRange false (fun _ -> ()) in
      Stream.iter (fun _ -> ()) tokenStream;
      if not (stop#is_end) && (!in_comment, !in_ghost_range) <> (stopIsInComment, stopIsInGhostRange) then
        perform_syntax_highlighting tab stop buffer#end_iter
    in
    match !path with
      None -> ()
    | Some path ->
      if Filename.check_suffix path ".c" then highlight (veri_keywords @ c_keywords)
      else if Filename.check_suffix path ".h" then highlight (veri_keywords @ c_keywords)
      else if Filename.check_suffix path ".java" then highlight (veri_keywords @ java_keywords)
      else ()
  in
  let add_buffer() =
    let path = ref None in
    let textLabel = GMisc.label ~text:"(untitled)" () in
    let textScroll =
      GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~shadow_type:`IN
        ~packing:(fun widget -> ignore (textNotebook#append_page ~tab_label:textLabel#coerce widget)) () in
    let srcText = GText.view ~packing:textScroll#add () in
    let buffer = srcText#buffer in
    let _ = buffer#create_tag ~name:"keyword" [`WEIGHT `BOLD; `FOREGROUND "Blue"] in
    let ghostRangeTag = buffer#create_tag ~name:"ghostRange" [`FOREGROUND "#CC6600"] in
    let _ = buffer#create_tag ~name:"ghostKeyword" [`WEIGHT `BOLD; `FOREGROUND "#DB9900"] in
    let commentTag = buffer#create_tag ~name:"comment" [`FOREGROUND "#008000"] in
    let _ = buffer#create_tag ~name:"ghostRangeDelimiter" [`FOREGROUND "Gray"] in
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
    srcText#set_pixels_above_lines 1;
    srcText#set_pixels_below_lines 1;
    subText#set_pixels_above_lines 1;
    subText#set_pixels_below_lines 1;
    let undoList: undo_action list ref = ref [] in
    let redoList: undo_action list ref = ref [] in
    let tab = (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) in
    buffer#connect#modified_changed (fun () ->
      updateBufferTitle tab
    );
    srcText#event#connect#key_press (fun key ->
      if GdkEvent.Key.keyval key = GdkKeysyms._Return then
      begin
        let cursor = buffer#get_iter `INSERT in
        let lineStart = cursor#set_line_offset 0 in
        let rec iter home =
          if home#ends_line then home else if Glib.Unichar.isspace home#char then iter home#forward_char else home
        in
        let home = iter lineStart in
        let indent = lineStart#get_text ~stop:home in
        buffer#insert ("\n" ^ indent);
        srcText#scroll_mark_onscreen `INSERT;
        true
      end
      else
        false
    );
    buffer#connect#insert_text (fun iter text ->
      if not !ignore_text_changes then
      begin
        let offset = iter#offset in
        undoList :=
          begin
            match !undoList with
              Insert (offset0, text0)::acs when offset = offset0 + String.length text0 ->
              Insert (offset0, text0 ^ text)::acs
            | acs -> Insert (offset, text)::acs
          end;
        redoList := [];
        undoAction#set_sensitive true;
        redoAction#set_sensitive false
      end
    );
    buffer#connect#after#insert_text (fun iter text ->
      let start = iter#backward_chars (Glib.Utf8.length text) in
      perform_syntax_highlighting tab start iter
    );
    buffer#connect#after#delete_range (fun ~start:start ~stop:stop ->
      perform_syntax_highlighting tab start stop
    );
    buffer#connect#delete_range (fun ~start:start ~stop:stop ->
      if not !ignore_text_changes then
      begin
        let offset = start#offset in
        let text = buffer#get_text ~start:start ~stop:stop () in
        undoList := 
          begin
            match !undoList with
              Delete (offset0, text0)::acs when offset = offset0 ->
              Delete (offset0, text0 ^ text)::acs
            | acs -> Delete (offset, text)::acs
          end;
        redoList := [];
        undoAction#set_sensitive true;
        redoAction#set_sensitive false
      end
    );
    buffer#connect#changed (fun () -> !bufferChangeListener tab);
    let focusIn _ = set_current_tab (Some tab); false in
    srcText#event#connect#focus_in ~callback:focusIn;
    subText#event#connect#focus_in ~callback:focusIn;
    buffers := !buffers @ [tab];
    tab
  in
  let updateMessageEntry() =
    match !msg with
      None -> messageEntry#coerce#misc#hide()
    | Some msg ->
      let (backColor, textColor) = if msg = "0 errors found" then ("green", "black") else ("red", "white") in
      messageEntry#coerce#misc#show();
      messageEntry#set_text msg;
      messageEntry#coerce#misc#modify_base [`NORMAL, `NAME backColor];
      messageEntry#coerce#misc#modify_text [`NORMAL, `NAME textColor]
  in
  let load ((path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) newPath =
    try
      let chan = open_in newPath in
      let rec iter () =
        let buf = String.create 60000 in
        let result = input chan buf 0 60000 in
        if result = 0 then [] else (String.sub buf 0 result)::iter()
      in
      let chunks = iter() in
      let _ = close_in chan in
      ignore_text_changes := true;
      buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter;
      let gIter = buffer#start_iter in
      List.iter (fun chunk -> (buffer: GText.buffer)#insert ~iter:gIter chunk) chunks;
      ignore_text_changes := false;
      undoList := [];
      redoList := [];
      buffer#set_modified false;
      path := Some (Filename.concat (Filename.dirname newPath) (Filename.basename newPath));
      perform_syntax_highlighting tab buffer#start_iter buffer#end_iter;
      updateBufferTitle tab
    with Sys_error msg -> GToolbox.message_box "VeriFast IDE" ("Could not load file: " ^ msg)
  in
  begin
    let tab = add_buffer() in
    set_current_tab (Some tab);
    match initialPath with None -> () | Some path -> load tab path
  end;
  let store ((path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) thePath =
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
  let save ((path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) =
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
    List.iter (fun ((path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) ->
      buffer#remove_tag_by_name "currentLine" ~start:buffer#start_iter ~stop:buffer#end_iter;
      buffer#remove_tag_by_name "currentCaller" ~start:buffer#start_iter ~stop:buffer#end_iter
    ) !buffers;
    assumptionsStore#clear();
    chunksStore#clear();
    srcEnvStore#clear();
    subEnvStore#clear()
  in
  let tab_path (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) = path in
  let tab_buffer (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) = buffer in
  let tab_srcText (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) = srcText in
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
          if textPaned#max_position - textPaned#position < 10 then
            textPaned#set_position 0;
          apply_tag_by_loc "currentLine" l;
          let ((path, line, col), _) = l in
          let (k, (_, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark)) = get_tab_for_path (string_of_path path) in
          textNotebook#goto_page k;
          buffer#move_mark (`MARK currentStepMark) ~where:(srcpos_iter buffer (line, col));
          Glib.Idle.add(fun () -> srcText#scroll_to_mark ~within_margin:0.2 (`MARK currentStepMark); false);
          append_items srcEnvStore srcEnvKCol srcEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups env))
        | (caller_loc, caller_env)::_ ->
          if textPaned#max_position >= 300 && textPaned#position < 10 || textPaned#max_position - textPaned#position < 10 then
            textPaned#set_position 150;
          begin
            apply_tag_by_loc "currentLine" l;
            let ((path, line, col), _) = l in
            let (k, (_, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark)) = get_tab_for_path (string_of_path path) in
            subNotebook#goto_page k;
            buffer#move_mark (`MARK currentStepMark) ~where:(srcpos_iter buffer (line, col));
            Glib.Idle.add (fun () -> subText#scroll_to_mark ~within_margin:0.2 (`MARK currentStepMark); false); 
            append_items subEnvStore subEnvKCol subEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups env))
          end;
          begin
            apply_tag_by_loc "currentCaller" caller_loc;
            let ((path, line, col), _) = caller_loc in
            let (k, (_, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark)) = get_tab_for_path (string_of_path path) in
            textNotebook#goto_page k;
            buffer#move_mark (`MARK currentCallerMark) ~where:(srcpos_iter buffer (line, col));
            Glib.Idle.add(fun () -> srcText#scroll_to_mark ~within_margin:0.2 (`MARK currentCallerMark); false);
            append_items srcEnvStore srcEnvKCol srcEnvCol (List.map (fun (x, t) -> x ^ "=" ^ t) (remove_dups caller_env))
          end
      end;
      let _ = append_items assumptionsStore assumptionsKCol assumptionsCol (List.rev ass) in
      let _ = append_items chunksStore chunksKCol chunksCol (List.map Verifast.string_of_chunk h) in
      ()
  in
  let _ = stepList#connect#cursor_changed ~callback:stepSelected in
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
      updateMessageEntry();
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
  let close ((_, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) as tab) =
    if not (ensureSaved tab) then
    begin
      textNotebook#remove textScroll#coerce;
      subNotebook#remove subScroll#coerce;
      buffers := List.filter (fun tab0 -> not (tab0 == tab)) !buffers;
      match !current_tab with None -> () | Some tab0 -> if tab == tab0 then set_current_tab None
    end
  in
  (actionGroup#get_action "Save")#connect#activate (fun () -> match get_current_tab() with Some tab -> save tab; () | None -> ());
  (actionGroup#get_action "SaveAs")#connect#activate (fun () -> match get_current_tab() with Some tab -> saveAs tab; () | None -> ());
  (actionGroup#get_action "Close")#connect#activate (fun () -> match get_current_tab() with Some tab -> close tab; () | None -> ());
  let handleStaticError l emsg =
    apply_tag_by_loc "error" l;
    msg := Some emsg;
    updateMessageEntry();
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
  let reportRange kind l =
    apply_tag_by_loc (tag_name_of_range_kind kind) l
  in
  let ensureHasPath tab =
    match !(tab_path tab) with
      None -> save tab
    | Some path ->
      if (tab_buffer tab)#modified then store tab path else Some path
  in
  let undo () =
    match get_current_tab() with
      None -> ()
    | Some (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) ->
      begin
        match !undoList with
          [] -> ()
        | ac::acs ->
          ignore_text_changes := true;
          let offset =
            match ac with
              Insert (offset, text) ->
              let start = buffer#get_iter (`OFFSET offset) in
              let stop = buffer#get_iter (`OFFSET (offset + String.length text)) in
              buffer#delete ~start:start ~stop:stop;
              offset
            | Delete (offset, text) ->
              let start = buffer#get_iter (`OFFSET offset) in
              buffer#insert ~iter:start text;
              offset + String.length text
          in
          ignore_text_changes := false;
          undoList := acs;
          redoList := ac::!redoList;
          undoAction#set_sensitive (acs <> []);
          redoAction#set_sensitive true;
          buffer#place_cursor ~where:(buffer#get_iter (`OFFSET offset));
          srcText#scroll_to_mark ~within_margin:0.2 `INSERT 
      end
  in
  let redo () =
    match get_current_tab() with
      None -> ()
    | Some (path, buffer, undoList, redoList, (textLabel, textScroll, srcText), (subLabel, subScroll, subText), currentStepMark, currentCallerMark) ->
      begin
        match !redoList with
          [] -> ()
        | ac::acs ->
          ignore_text_changes := true;
          let offset =
            match ac with
              Insert (offset, text) ->
              let start = buffer#get_iter (`OFFSET offset) in
              buffer#insert ~iter:start text;
              offset + String.length text
            | Delete (offset, text) ->
              let start = buffer#get_iter (`OFFSET offset) in
              let stop = buffer#get_iter (`OFFSET (offset + String.length text)) in
              buffer#delete ~start:start ~stop:stop;
              offset
          in
          ignore_text_changes := false;
          redoList := acs;
          undoList := ac::!undoList;
          undoAction#set_sensitive true;
          redoAction#set_sensitive (acs <> []);
          buffer#place_cursor ~where:(buffer#get_iter (`OFFSET offset));
          srcText#scroll_to_mark ~within_margin:0.2 `INSERT
      end
  in
  let verifyProgram runToCursor () =
    clearTrace();
    List.iter (fun tab ->
      let buffer = tab_buffer tab in
      buffer#remove_all_tags ~start:buffer#start_iter ~stop:buffer#end_iter
    ) !buffers;
    match get_current_tab() with
      None -> ()
    | Some tab ->
      begin
        match ensureHasPath tab with
          None -> ()
        | Some path ->
          begin
            let breakpoint =
              if runToCursor then
              begin
                let buffer = tab_buffer tab in
                let insert_iter = buffer#get_iter_at_mark `INSERT in
                let insert_line = insert_iter#line in
                Some (path, insert_line + 1)
              end
              else
                None
            in
            try
              let options = {option_verbose = false; option_disable_overflow_check = !disableOverflowCheck; option_allow_should_fail = true} in
              verify_program None false options path reportRange breakpoint;
              msg := Some (if runToCursor then "0 errors found (cursor is unreachable)" else "0 errors found");
              updateMessageEntry()
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
                updateMessageEntry()
              end
              else
                handleStaticError l emsg
            | e ->
              prerr_endline ("VeriFast internal error: " ^ Printexc.to_string e);
              Printexc.print_backtrace stderr;
              flush stderr;
              GToolbox.message_box "VeriFast IDE" "Verification failed due to an internal error. See the console window for details."
          end
      end
  in
  (actionGroup#get_action "VerifyProgram")#connect#activate (verifyProgram false);
  (actionGroup#get_action "RunToCursor")#connect#activate (verifyProgram true);
  undoAction#connect#activate undo;
  redoAction#connect#activate redo;
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
