
let show_stack s =
  Format.printf "==> stack [%a]@." (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") (fun ppf (fn, d, ar, args) -> Format.fprintf ppf "(%a, %d, %d, [%a])" Printtyp.longident fn d ar (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ";") Format.pp_print_string) args)) s

let for_complete_calls ~on_start ~on_end ~on_call ~on_ret () =
  let stack = ref [] in
  fun ppf t ->
    let debug_stack = false in
    let debug_trace = false in
    if debug_stack then show_stack !stack;
    match t with
    | Trace.Call (fn, d, ar, l, v, t) ->
      if debug_trace then
        Format.fprintf ppf "@[<2>%a %d <--@ %s%a@]@."
        Printtyp.longident fn d
        (Printtyp.string_of_label l)
        (Topeval.print_value !Topcommon.toplevel_env v)
        t;
      begin match !stack with
        | (f, d1, _dm, args) :: tl when f = fn && d-1 = d1 ->
          let args = Format.asprintf "%a" (Topeval.print_value !Topcommon.toplevel_env v) t :: args in
          stack := (f, d, ar, args) :: tl;
          if d = ar-1 then on_call ppf fn (List.rev args)
        | _ ->
          (match !stack with | [] -> on_start ppf | _ -> ());
          let args = [Format.asprintf "%a" (Topeval.print_value !Topcommon.toplevel_env v) t] in
          stack := (fn, d, ar, args) :: !stack;
          if d = ar-1 then on_call ppf fn args
      end
    | Ret (fn, d, ar, res, t) ->
     if debug_trace then
      Format.fprintf ppf "@[<2>%a %d -->@ %a@]@."
        Printtyp.longident fn d
        (Topeval.print_value !Topcommon.toplevel_env res) t;
        begin match !stack with
        | [] ->
          Format.printf "trying to return from empty stack@.";
          assert false
        | (f, _d1, _m, args) :: tl when f = fn && Int.equal d (ar-1) ->
          stack := tl;
          on_ret ppf fn (List.rev args) (Format.asprintf "%a" (Topeval.print_value !Topcommon.toplevel_env res) t);
          (match tl with [] -> on_end ppf | _ -> ())
        | _ -> ()
        end
    | Exn (fn, d, ar, ex) ->
    if debug_trace then
      Format.fprintf ppf "@[<2>%a %d raises@ %a@]@."
        Printtyp.longident fn d
        (Topeval.print_value !Topcommon.toplevel_env (Obj.repr ex)) Predef.type_exn;
        (* this case is very similar to ret. it pops from the stack and may call on_end *)
        begin match !stack with
        | [] ->
          Format.printf "trying to raise at empty stack@.";
          assert false
        | (f, _d1, _m, args) :: tl when f = fn && Int.equal d (ar-1) ->
          stack := tl;
          on_ret ppf fn (List.rev args) (Format.asprintf "%s" (Printexc.to_string ex));
          (match tl with [] -> on_end ppf | _ -> ())
        | _ -> ()
        end

let _default_trace_hook_txt =
  for_complete_calls
    (* ~on_start:(fun _ppf -> ()) *)
    (* ~on_end:(fun _ppf -> ()) *)
    ~on_start:(fun ppf -> Format.fprintf ppf "start@.")
    ~on_end:(fun ppf -> Format.fprintf ppf "end@.")
    ~on_call:(fun ppf fn args ->
      Format.fprintf ppf "%a: (%a)@."
        Printtyp.longident fn
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") Format.pp_print_string) args)
    ~on_ret:(fun ppf fn args res ->
      Format.fprintf ppf "%a: (%a) => %s@."
        Printtyp.longident fn
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") Format.pp_print_string) args res)
    ()

let _default_trace_hook_block =
  for_complete_calls
    (* ~on_start:(fun _ppf -> ()) *)
    (* ~on_end:(fun _ppf -> ()) *)
    ~on_start:(fun ppf -> Format.fprintf ppf "start@.")
    ~on_end:(fun ppf -> Format.fprintf ppf "end@.")
    ~on_call:(fun _ppf _fn _args -> ())
    ~on_ret:(fun ppf fn args res ->
      let i = ref 0 in
      Format.fprintf ppf "%a\n%a\nres: %s\n@."
        Printtyp.longident fn
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n") (fun ppf s -> Format.fprintf ppf "arg %d: %s" (!i+1) s; incr i)) args res)
    ()

let _default_trace_hook_chrome =
  for_complete_calls
    ~on_start:(fun ppf -> Format.fprintf ppf "[@.")
    ~on_end:(fun _ppf -> ())
    ~on_call:(fun ppf fn args ->
      let i = ref 0 in
      Format.fprintf ppf {|{"ph": "B", "name": "%a", "ts": "%d", "args": {%a}}@.|}
        Printtyp.longident fn
        (int_of_float (Sys.time () *. 1_000_000.))
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ") (fun ppf a -> Format.fprintf ppf {|"arg %d": "%s"|} (!i+1) (String.escaped a); incr i)) args)
    ~on_ret:(fun ppf fn _args res ->
      Format.fprintf ppf {|{"ph": "E", "name": "%a", "ts": "%d", "args": {"res": "%s"}}@.|}
        Printtyp.longident fn
        (int_of_float (Sys.time () *. 1_000_000.))
        (String.escaped res))
    ()

module Zipper = struct
  type 'a tree =
    | Section of {
        item : 'a;
        children : 'a tree list;
      }

  let rec pp_tree pp_a ppf (Section {item; children}) =
    (* Format.fprintf ppf "[%a](%a)" pp_a item (Format.Format.pp_print_list ~pp_sep:(fun ppf () -> Format.Format.fprintf ppf ",") (pp_tree pp_a)) children *)
    Format.fprintf ppf {|{"%a": [%a]}|} pp_a item (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") (pp_tree pp_a)) children

  type 'a path =
    | Top
    | Node of 'a * 'a tree list * 'a path * 'a tree list

  type 'a location = Loc of 'a tree * 'a path

  let _go_left (Loc (t, p)) =
    match p with
    | Top -> failwith "left of top"
    | Node (a, l :: left, up, right) -> Loc (l, Node (a, left, up, t :: right))
    | Node (_a, [], _up, _right) -> failwith "left of first"

  let _go_right (Loc (t, p)) =
    match p with
    | Top -> failwith "right of top"
    | Node (a, left, up, r :: right) -> Loc (r, Node (a, t :: left, up, right))
    | _ -> failwith "right of last"

  let go_up (Loc (t, p)) =
    match p with
    | Top -> failwith "up of top"
    | Node (a, left, up, right) ->
      Loc (Section { item = a; children = List.rev left @ (t :: right) }, up)

  let go_down (Loc (t, p)) =
    match t with
    | Section { item; children = t1 :: trees } ->
      Loc (t1, Node (item, [], p, trees))
    | _ -> failwith "down of empty"

  let add_child ch (Loc (Section { item; children }, p)) =
    Loc
      ( Section
          { item; children = Section { item = ch; children = [] } :: children },
        p )

  let close_node ?i (Loc (Section { item; children }, p)) =
    let l = Loc (Section { item = i |> Option.value ~default:item; children = List.rev children }, p) in
    go_up l

  let emp = Loc (Section { item = "root"; children = [] }, Top)
end

let _default_trace_hook_tree =
  let tree = ref Zipper.emp in
  let handle =
    for_complete_calls
      ~on_call:(fun _ppf fn args ->
        let call = Format.asprintf "%a: (%a)"
            Printtyp.longident fn
            (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") Format.pp_print_string) args
        in
        tree := !tree |> Zipper.add_child call |> Zipper.go_down)
      ~on_ret:(fun _ppf fn args res ->
        let call = Format.asprintf "%a: (%a) => %s"
            Printtyp.longident fn
            (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") Format.pp_print_string) args res
        in
        tree := !tree |> Zipper.close_node ~i:call)
      ~on_end:(fun _ppf ->
        let (Loc (t, _)) = !tree in
        Format.printf "%a@." (Zipper.pp_tree Format.pp_print_string) t
      )
      ~on_start:(fun _ppf -> ())
      ()
  in
  fun ppf t -> handle ppf t


let () =
  (* Trace.trace_hook := _default_trace_hook_txt; *)
  (* Trace.trace_hook := _default_trace_hook_tree; *)
  (* Trace.trace_hook := _default_trace_hook_block; *)
  Trace.trace_hook := _default_trace_hook_chrome;
  exit (Topmain.main ())
