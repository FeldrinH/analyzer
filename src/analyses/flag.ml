(** Analysis for the OSEK flag pattern. *)

open Prelude.Ana
open Analyses

module Spec =
struct
  include Analyses.DefaultSpec

  module D = Lattice.Unit
  module C = Lattice.Unit
  module G = Lattice.Unit

  module Val = IntDomain.Flattened
  module VSet = SetDomain.ToppedSet(Val)(struct let topname = "Various" end)

  let vars : (string , VSet.t) Hashtbl.t = Hashtbl.create 16
  let flags = ref ([] : string list)
  let noflags = ref ([] : string list)
  let flagmax = 3
  let branchvars = ref ([] : string list)

  (* transfer functions *)

  let listrem x l = List.filter (fun y -> not( x=y)) l

  let rec no_addr_of_flag expr =
    match expr with
    | Const _
    | SizeOf _
    | SizeOfE _
    | SizeOfStr _
    | AlignOf _
    | AlignOfE _  -> ()
    | UnOp (_,e,_)
    | Real e
    | Imag e -> no_addr_of_flag e
    | BinOp (_,e1,e2,_) -> no_addr_of_flag e1; no_addr_of_flag e2
    | Lval (Var _,o) -> ()
    | AddrOf (Var vinfo,o)
    | StartOf (Var vinfo,o) -> flags := listrem vinfo.vname !flags; noflags := vinfo.vname :: !noflags
    | Lval (Mem e,o)    -> no_addr_of_flag e
    | AddrOf (Mem e,o)  -> no_addr_of_flag e
    | StartOf (Mem e,o) -> no_addr_of_flag e
    | CastE (t,e) -> no_addr_of_flag e
    | Question (e1, e2, e3, _) -> no_addr_of_flag e1; no_addr_of_flag e2; no_addr_of_flag e3
    | AddrOfLabel _ -> ()


  let assign ctx (lval:lval) (rval:exp) : D.t =
    (* let _ = print_endline ( "assign") in       *)
    let _ = no_addr_of_flag rval in
    let _ = match lval with
      | (Var var, NoOffset) -> if var.vglob then begin
          let x = var.vname in if List.mem x !noflags then () else
            (* let _ = print_endline ( List.fold_left (fun acc a -> a ^ ", " ^ acc) "" !flags   ) in  *)
            (match rval with
             | Const (CInt64 (i,_,_)) -> if List.mem x !flags then
                 let v = Hashtbl.find vars x in
                 (* let _ = print_endline ( "assign" ^ (Int64.to_string i)) in   *)
                 (* let _ = print_endline ( x ^ " has values " ^ VSet.fold (fun e str -> (Val.short 50 e) ^", " ^str  ) v " ") in       *)
                 if (VSet.mem (Val.of_int i) v) then () else
                 if (VSet.cardinal v < flagmax) then
                   (* let _ = print_endline ( "add") in   *)
                   Hashtbl.replace vars x (VSet.add (Val.of_int i) v)
                 else begin
                   (* let _ = print_endline ( "remove") in   *)
                   flags := listrem x !flags;
                   branchvars := listrem x !branchvars;
                   noflags := x::!noflags;
                   Hashtbl.remove vars x
                 end
               else begin
                 flags := x ::!flags;
                 Hashtbl.add vars x (VSet.add (Val.of_int i) (VSet.empty ()) )
               end
             | _ ->
               noflags := x::!noflags; if List.mem x !flags then begin
                 flags := listrem x !flags;
                 Hashtbl.remove vars x
               end
            )
        end
      | _ -> ()
    in D.top ()

  let rec check var =
    let doit var = if (var.vglob && (not(List.mem var.vname !noflags)) && (not (List.mem var.vname 	!branchvars))) then
        branchvars := var.vname :: !branchvars
      else ()
    in match var with
    | Const _ -> ()
    | Lval (Var var,_) -> doit var
    | BinOp (_,arg1,arg2,_) ->
      check arg1;
      check arg2
    | UnOp (_,arg1,_) ->
      check arg1
    | AddrOf (Var var,_)  -> doit var
    | StartOf (Var var,_) -> doit var
    | CastE  (_, exp) -> check exp
    | _ -> ()

  let branch ctx (exp:exp) (tv:bool) : D.t =
    let _ = no_addr_of_flag exp in
    let _ = check exp in
    D.top ()

  let body ctx (f:fundec) : D.t = D.top ()

  let return ctx (exp:exp option) (f:fundec) : D.t = let _ = BatOption.may no_addr_of_flag exp in D.top ()

  (*   let eval_funvar ctx (fv:exp) =  [(ctx.local,ctx.local)] *)

  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    let _ = List.iter no_addr_of_flag args in
    [(D.top (),D.top ())]

  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) fc (au:D.t) : D.t =
    let _ = List.iter no_addr_of_flag args in
    let _ = no_addr_of_flag fexp in
    D.top ()

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    let _ = List.iter no_addr_of_flag arglist in
    match f.vname with _ -> D.top ()

  let startstate v = D.top ()
  let threadenter ctx lval f args = [D.top ()]
  let threadspawn ctx lval f args fctx = ctx.local
  let exitstate  v = D.top ()

  let name () = "flag"

  let should_join _ _ = true

  (** postprocess and print races and other output *)
  let finalize () =
    let sprint f x = BatPrintf.fprintf f "\"%s\"" x in
    let print_flags_file f =
      BatPrintf.fprintf f "{\n\"ana\": {\n\t\"osek\": {\n\t\t\"flags\": %a\n\t\t}\n\t}\n}\n"
        (BatList.print ~sep:", " sprint)
        (List.filter (fun x -> (List.mem x !branchvars)) !flags)
    in
    BatFile.with_file_out "flags.json" print_flags_file

  let init () =  ()

end

let _ =
  MCP.register_analysis (module Spec : MCPSpec)
