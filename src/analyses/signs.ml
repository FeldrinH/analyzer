(** An analysis specification for didactic purposes. *)

open Prelude.Ana
open Analyses

(* Sign domain. Has top, bot and all possible combinations of signs*)
module Signs =
struct
  (* Sign, with three boolean values representing possibility of value having minus, zero or plus sign respectively *)
  type t = Sign of bool * bool * bool [@@deriving eq, to_yojson]
  let name () = "signs"

  let top () = Sign(true, true, true)
  let bot () = Sign(false, false, false)

  let is_top x = x = top ()
  let is_bot x = x = bot ()

  let show = function
   | Sign(true, true, true) -> "top"
   | Sign(false, false, false) -> "bot"
   | Sign(true, false, false) -> "-"
   | Sign(false, false, true) -> "+"
   | Sign(false, true, false) -> "0"
   | Sign(true, true, false) -> "0/-"
   | Sign(false, true, true) -> "0/+"
   | Sign(true, false, true) -> "+/-"

  module P =
  struct
    type t' = t
    let name = name
    let show = show
  end
  include Printable.StdPolyCompare
  include Printable.PrintSimple (P)

  let hash = Hashtbl.hash

  let equal_to i x = failwith "equal_to unimplemented"
  let leq (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = n1 <= n2 && z1 <= z2 && p1 <= p2
  let join (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(n1 || n2, z1 || z2, p1 || p2)
  let widen = join (* is this ok? *)
  let meet (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(n1 && n2, z1 && z2, p1 && p2)
  let narrow = meet (* is this ok? *)

  let of_bool x = if x then Sign(false,false,true) else Sign(false,true,false)
  let to_bool = function
   | Sign(true,false,_) | Sign(_,false,true) -> Some(true)
   | Sign(false,true,false) -> Some(false)
   | _ -> None
  let is_bool x = to_bool x <> None

  let of_int x =
    if x < Int64.zero then Sign(true, false, false)
    else if x > Int64.zero then Sign(false, false, true)
    else Sign(false, true, false)
  let to_int = function
   (* is this valid? *)
   | Sign(false,true,false) -> Some(0L)
   | _ -> None
  let is_int x = to_int x <> None

  (* helper function to ensure operations with bot always result in bot *)
  let propagate_bot f x y = if is_bot x || is_bot y then bot () else f x y

  let neg (Sign(n,z,p)) = Sign(p, z, n)
  let add (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(
    n1 || n2,
    z1 && z2 || n1 && p2 || p1 && n2,
    p1 || p2
  )
  let sub (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(
    n1 || p2,
    z1 && z2 || n1 && n2 || p1 && p2,
    p1 || n2
  )
  let mul' (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(
    n1 && p2 || p1 && n2,
    z1 || z2,
    n1 && n2 || p1 && p2
  )
  let mul = propagate_bot mul'
  let div' (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(
    n1 && p2 || p1 && n2,
    n2 || p2,
    n1 && n2 || p1 && p2
  )
  let div = propagate_bot div'
  let rem (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = failwith "remainder unimplemented"

  let lognot (Sign(n,z,p)) = Sign(false, p || n, z)
  let logand' (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) =
    let t1 = n1 || p1 in let t2 = n2 || p2 in Sign(false, z1 || z2, t1 && t2)
  let logand = propagate_bot logand'
  let logor' (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) =
    let t1 = n1 || p1 in let t2 = n2 || p2 in Sign(false, z1 && z2, t1 || t2)
  let logor = propagate_bot logor'

  let lt' (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(
    false,
    p1 || n2 || z1 && z2,
    n1 || p2
  )
  let lt = propagate_bot lt'
  let gt x y = lt y x
  let le x y = lognot (gt x y)
  let ge x y = lognot (lt x y)

  let eq' (Sign(n1,z1,p1)) (Sign(n2,z2,p2)) = Sign(
    false,
    n1 || p1 || n2 || p2,
    n1 && n2 || z1 && z2 || p1 && p2
  )
  let eq = propagate_bot eq'
  let ne x y = lognot (eq x y)

  let cast_to ?torg t x = failwith "cast_to unimplemented"
  let arbitrary () = failwith "arbitrary unimplemented"
end

module Spec : Analyses.MCPSpec =
struct
  include Analyses.DefaultSpec

  let name () = "signs"
  module D = MapDomain.MapBot (Basetype.Variables) (Signs)
  module G = Lattice.Unit
  module C = D

  (* transfer functions *)
  let rec eval (d: D.t) (exp: exp): Signs.t = match exp with
    | Const (CInt64 (i, _, _)) -> Signs.of_int i
    | Lval (Var x, NoOffset) -> D.find x d
    | UnOp (op, e, _) -> begin
      let s = eval d e in
      match op with
      | Neg -> Signs.neg s
      | _ -> failwith "unary operator not implemented"
    end
    | BinOp (op, e1, e2, _) -> begin
      let s1 = eval d e1 and s2 = eval d e2 in
      match op with
      | PlusA -> Signs.add s1 s2
      | MinusA -> Signs.sub s1 s2
      | Mult -> Signs.mul s1 s2
      | Div -> Signs.div s1 s2
      | Eq -> Signs.eq s1 s2
      | Ne -> Signs.ne s1 s2
      | Gt -> Signs.gt s1 s2
      | Lt -> Signs.lt s1 s2
      | Ge -> Signs.ge s1 s2
      | Le -> Signs.le s1 s2
      | _ -> failwith "binary operator not implemented"
    end
    | _ -> Signs.top ()

  let assign ctx (lval:lval) (rval:exp) : D.t =
    let d = ctx.local in
    match lval with
    | Var x, NoOffset -> D.add x (eval d rval) d
    | _ -> D.top ()

  let branch ctx (exp:exp) (tv:bool) : D.t =
    ctx.local

  let body ctx (f:fundec) : D.t =
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : D.t =
    ctx.local

  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    [ctx.local, ctx.local]

  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) fc (au:D.t) : D.t =
    au

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    ctx.local

  let assert_holds (d: D.t) (e: exp) = match e with
  | BinOp (op, e1, e2, _) -> Signs.to_bool (eval d e)
  | _ -> None

  let query ctx (type a) (q: a Queries.t): a Queries.result =
    let open Queries in
    match q with
    | Assert e -> begin
      match assert_holds ctx.local e with
      | Some(true) -> `Lifted true
      | Some(false) -> `Lifted false
      | None -> Result.top q
    end
    | _ -> Result.top q

  let startstate v = D.bot ()
  let threadenter ctx lval f args = [D.top ()]
  let threadspawn ctx lval f args fctx = ctx.local
  let exitstate  v = D.top ()
end

let _ =
  MCP.register_analysis (module Spec : MCPSpec)
