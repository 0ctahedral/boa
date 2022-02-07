open Printf
open Exprs
open Pretty

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EId _ -> true
  | _ -> false
;;

(* PROBLEM 1 *)
(* This function should encapsulate the binding-error checking from Boa *)
let rec is_in_env (name: string) (env: string list) : bool =
  match env with
    | [] -> false
    | first::rest -> if name = first then true else (is_in_env name rest)

exception BindingError of string
let check_scope (e : (Lexing.position * Lexing.position) expr) : unit =
  let rec check_env (e : (Lexing.position * Lexing.position) expr) (env: string list) : unit =
    match e with
      | ENumber(_, _) -> ()
      | EId(name, pos) -> if (is_in_env name env) then ()
                          else raise (BindingError (sprintf "%s not in scope at %s" name (string_of_pos pos)))
      | EPrim1(_, e, _) -> check_env e env
      | EPrim2(_, e1, e2, _) -> let _ = check_env e1 env in check_env e2 env
      | ELet(binds, body, _) -> let (acc_env, _) = List.fold_left_map (
        fun acc_env (x, e, pos) -> if (is_in_env x acc_env) then
                              raise (BindingError (sprintf "%s already bound in this let expression at %s" x (string_of_pos pos)))
                                  else
                                    let _ = check_env e (acc_env @ env) in
                                    (x::acc_env, ())
        ) [] binds in
        check_env body (acc_env @ env)
      | EIf(cond, thn, els, _) -> let _ = check_env cond env in
                                    let _ = check_env thn env in
                                      check_env els env
  in
  check_env e []
 
type tag = int


(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (cur : tag) : (tag expr * tag) =
    match e with
    | EId(x, _) -> (EId(x, cur), (cur + 1))
    | ENumber(n, _) -> (ENumber(n, cur), (cur + 1))
    | EPrim1(op, e, _) ->
      let (tagged_e, next_tag) = help e (cur + 1) in
      (EPrim1(op, tagged_e, cur), next_tag)
    | EPrim2(op, e1, e2, _) ->
      let (tagged_e1, pass_tag) = help e1 (cur + 1) in
      let (tagged_e2, next_tag) = help e2 pass_tag in
      (EPrim2(op, tagged_e1, tagged_e2, cur), next_tag)
    | ELet(binds, body, _) ->
      let (bind_next_tag, tagged_binds) = List.fold_left_map(
        fun cur bind -> 
          let (x, e, _) = bind in
          let (tagged_e, next_tag) = help e (cur + 1) in
          (next_tag, (x, tagged_e, cur))
      ) (cur + 1) binds in
      let (tagged_body, next_tag) = (help body bind_next_tag) in
      (ELet(tagged_binds, tagged_body, cur), next_tag)
    | EIf(cond, thn, els, _) ->
      let (tagged_cond, cond_next_tag) = help cond (cur + 1) in
      let (tagged_thn, thn_next_tag) = help thn cond_next_tag in
      let (tagged_els, els_next_tag) = help els thn_next_tag in
       (EIf(tagged_cond, tagged_thn, tagged_els, cur), els_next_tag)
  in
  let (tagged, _) = help e 0 in tagged;
;;

(* This function removes all tags, and replaces them with the unit value.
   This might be convenient for testing, when you don't care about the tag info. *)
let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId(x, _) -> EId(x, ())
  | ENumber(n, _) -> ENumber(n, ())
  | EPrim1(op, e, _) ->
     EPrim1(op, untag e, ())
  | EPrim2(op, e1, e2, _) ->
     EPrim2(op, untag e1, untag e2, ())
  | ELet(binds, body, _) ->
     ELet(List.map(fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf(cond, thn, els, _) ->
     EIf(untag cond, untag thn, untag els, ())
;;

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

(* PROBLEM 3 *)
let rename (e : tag expr) : tag expr =
  let rec help (env : (string * string) list) (e : tag expr) =
    match e with
    | EId(x, tag) -> EId((find env x), tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EPrim1(op, e, tag) -> EPrim1(op, (help env e), tag)
    | EPrim2(op, e1, e2, tag) -> EPrim2(op, (help env e1), (help env e2), tag)
    | ELet(binds, body, tag) -> let (new_env, new_binds) = List.fold_left_map(
      fun env (x, e, x_tag) -> let new_x = sprintf "%s#%d" x x_tag in
                                let new_env = (x, new_x)::env in
                                let new_e = help new_env e in
                                (new_env, (new_x, new_e, x_tag))
      ) env binds in
      let new_body = help new_env body in
      ELet(new_binds, new_body, tag)
    | EIf(cond, thn, els, tag) -> EIf((help env cond), (help env thn), (help env els), tag)
  in help [] e
;;

(* PROBLEM 4 & 5 *)
(* This function converts a tagged expression into an untagged expression in A-normal form *)
let anf (e : tag expr) : unit expr =
  let rec gen_context (e : tag expr) : (unit expr * (string * unit expr) list) =
    match e with
    | ENumber _ | EId _ -> (untag e, [])
    | EPrim1(op, e, t) ->
        let (new_e, e_ctx)  = gen_context e in
        let id = sprintf "$prim1_%d" t in
          (EId(id, ()), e_ctx @ [(id, EPrim1(op, new_e, ()))])
    | EPrim2(op, e1, e2, t) ->
        let (new_e1, e1_ctx)  = gen_context e1 in
        let (new_e2, e2_ctx)  = gen_context e2 in
        let id = sprintf "$prim2_%d" t in
          (EId(id, ()), e1_ctx @ e2_ctx @ [(id, EPrim2(op, new_e1, new_e2, ()))])
    | EIf(cond, thn, els, t) ->
        (* TODO: anf the condition *)
        let (new_thn, thn_ctx)  = gen_context thn in
        let (new_els, els_ctx)  = gen_context els in
        let id = sprintf "$if_%d" t in
          (EId(id, ()), thn_ctx @ els_ctx @ [(id, EIf(untag cond, new_thn, new_els, ()))])
    | ELet(binds, body, _) ->
        let (new_body, body_ctx) = gen_context body in
        let (acc_ctx, _) = List.fold_left_map(
          fun ctx (x, b, _) -> 
            let (new_b, bind_ctx) = gen_context b in
            (ctx @ bind_ctx @ [(x, new_b)], ())
        ) [] binds in
          (new_body, acc_ctx @ body_ctx)
  in
  let rec context_to_expr (ans : unit expr) (ctx: (string * unit expr) list) : unit expr =
    List.fold_right(fun (name, e) ans -> ELet([(name, e, ())], ans, ())) ctx ans
  in
  let (ans, ctx) = gen_context e in
  let final = context_to_expr ans ctx in final
;;


(* Helper functions *)
let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "rax"
  | RSP -> "rsp"

let arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "QWORD %Ld" n
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
     if n >= 0 then
       sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
     else
       sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)

let i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
     sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub(dest, to_sub) ->
     sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul(dest, to_mul) ->
     sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ILabel(label) -> sprintf "%s:" label 
  | ICmp(dest, src) ->
      sprintf "  cmp %s, %s" (arg_to_asm dest) (arg_to_asm src)
  | IJne(label) -> sprintf "  jne %s" label
  | IJe(label) -> sprintf "  je %s" label
  | IJmp(label) -> sprintf "  jmp %s" label
  | IRet -> "  ret"

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is



(* PROBLEM 5 *)
(* This function actually compiles the tagged ANF expression into assembly *)
(* The si parameter should be used to indicate the next available stack index for use by Lets *)
(* The env parameter associates identifier names to stack indices *)
let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ENumber(n, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EId(x, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EPrim1(op, e, _) ->
     let e_reg = compile_imm e env in
     begin match op with
     | Add1 -> [
         IMov(Reg(RAX), e_reg);
         IAdd(Reg(RAX), Const(1L))
       ]
     | Sub1 -> [
         IMov(Reg(RAX), e_reg);
         IAdd(Reg(RAX), Const(Int64.minus_one))
       ]
     end
  | EPrim2(op, left, right, _) ->
      begin match op with
      | Plus  -> [
        IMov(Reg(RAX), compile_imm left env);
        IAdd(Reg(RAX), compile_imm right env)
      ]
      | Minus -> [
        IMov(Reg(RAX), compile_imm left env);
        ISub(Reg(RAX), compile_imm right env)
      ]
      | Times -> [
        IMov(Reg(RAX), compile_imm left env);
        IMul(Reg(RAX), compile_imm right env)
      ]
      end
  | EIf(cond, thn, els, tag) ->
      let tlabel = sprintf "%d_true" tag in
      (compile_expr cond si env) @
      [(*compare to zero, jump*)
        ICmp(Reg(RAX), Const(0L));
        IJe(tlabel)
      ] @
      [(*els label and condition, jump to done*)] @
      [(*thn label and condition*)] @
      [(*done label*)]
  | ELet([id, e, _], body, _) ->
      (compile_expr e (si + 1) env) @
      [
        IMov(RegOffset(-si, RSP), Reg(RAX));
      ] @ (compile_expr body (si + 1) ((id, si) :: env))
  | _ -> failwith "Impossible: Not in ANF"
and compile_imm e env =
  match e with
  | ENumber(n, _) -> Const(n)
  | EId(x, _) -> RegOffset(~-(find env x), RSP)
  | _ -> failwith "Impossible: not an immediate"


let compile_anf_to_string anfed =
  let prelude =
    "section .text
global our_code_starts_here
our_code_starts_here:" in
  let compiled = (compile_expr anfed 1 []) in
  let as_assembly_string = (to_asm (compiled @ [IRet])) in
  sprintf "%s%s\n" prelude as_assembly_string

    
let compile_to_string prog =
  check_scope prog;
  let tagged : tag expr = tag prog in
  let renamed : tag expr = rename tagged in
  let anfed : tag expr = tag (anf renamed) in
  (*
  printf "Prog:\n%s\n" (ast_of_expr prog);
  printf "Tagged:\n%s\n" (format_expr tagged string_of_int);
  printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int);
  *)
  compile_anf_to_string anfed

