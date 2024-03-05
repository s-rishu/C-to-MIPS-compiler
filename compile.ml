(* Compile Cish AST to MIPS AST *)
open Mips

exception IMPLEMENT_ME

type result = { code : Mips.inst list;
                data : Mips.label list }

(* generate fresh labels *)
let label_counter = ref 0
let new_int() = (label_counter := (!label_counter) + 1; !label_counter)
let new_label() = "L" ^ (string_of_int (new_int()))
let var_count = ref 0
let new_offset_table() = (Hashtbl.create 50)
(* generate a fresh temporary variable and store it in the variables set. *)
(* let rec new_temp() = 
    let t = "T" ^ (string_of_int (new_int())) in
    (* make sure we don't already have a variable with the same name! *)
    if (Hashtbl.mem (!offset_table) t) then new_temp()
    else (var_count := (!var_count) + 1; Hashtbl.add (!offset_table) t (-(!var_count)); t) *)

let reset() = (var_count := 0)
let rec set_args_offset (args: Ast.var list) (var_pos) (offset_table) = 
    match args with
    [] -> offset_table
    | hd :: tl -> (Hashtbl.add (offset_table) hd (var_pos); set_args_offset tl (var_pos+1) offset_table)

let rec collect_vars_count (p : Ast.stmt) offset_table = (
    let rec collect_vars_exp (e: Ast.exp) offset_table = (
        match e with
        (re, _) -> (
            match re with
            | Var(v) when (not (Hashtbl.mem (offset_table) v))-> (var_count := (!var_count) + 1; Hashtbl.add (offset_table) v (-(!var_count)); offset_table) (*assumes no nesting of same variable names*)
            | Binop(e1, b, e2) -> (collect_vars_exp e2 (collect_vars_exp e1 offset_table))
            | Not(e) -> (collect_vars_exp e offset_table)
            | And(e1, e2) -> (collect_vars_exp e2 (collect_vars_exp e1 offset_table))
            | Or(e1, e2) -> (collect_vars_exp e2 (collect_vars_exp e1 offset_table))
            | Assign(v, e) -> (collect_vars_exp e (collect_vars_exp (Var(v), 0) offset_table))
            | Call(v, e_hd::e_tl) -> (collect_vars_exp (Call(v, e_tl), 0) (collect_vars_exp e_hd offset_table))
            | _ -> (offset_table)
    ))
    in 
    (
    match p with 
    (rs, _) -> 
        match rs with
        | Exp(exp) -> (collect_vars_exp exp offset_table)                      
        | Seq(stmt1, stmt2) ->  (collect_vars_count stmt2 (collect_vars_count stmt1 offset_table))   
        | If(exp, stmt1, stmt2) -> (collect_vars_count stmt2 (collect_vars_count stmt1 (collect_vars_exp exp offset_table)))
        | While(exp, stmt) -> (collect_vars_count stmt (collect_vars_exp exp offset_table))
        | For(exp1, exp2, exp3, stmt) -> (collect_vars_count stmt (collect_vars_exp exp3 (collect_vars_exp exp2 (collect_vars_exp exp1 offset_table))))
        | Return(exp) -> (collect_vars_exp exp offset_table)
        | Let(v, exp, stmt) -> (collect_vars_count stmt (collect_vars_exp exp (collect_vars_exp (Var(v), 0) offset_table)))
    )
)


let rec compile_stmt ((s,_):Ast.stmt) (offset_table) : inst list = 
    let caller_prologue (callee: label) (args: Ast.exp list): inst list = (
      (* pass arguments, skip saving registers for now, jump and link *)
      (* [Sub(R29, R29, 4); Sw(R4, R29, Word32.fromInt 0);
      Sub(R29, R29, 4); Sw(R5, R29, Word32.fromInt 0);
      Sub(R29, R29, 4); Sw(R6, R29, Word32.fromInt 0);
      Sub(R29, R29, 4); Sw(R7, R29, Word32.fromInt 0);] @ *)
      (* generates mips code to save first four function actual args on the registers and others on stack *)
      let rec save_actual_args (args: Ast.exp list): inst list = (
        match args with
          | [] -> []
          | hd :: tl -> (save_actual_args tl) @ ((compile_stmt (Exp(hd), 0) offset_table) @ [Add(R3, R0, Immed(Word32.fromInt 4)); Sub(R29, R29, R3); Sw(R2, R29, Word32.fromInt 0)]) (*saving args in reverse order on stack*)
      ) in 
      (save_actual_args args) @ 
      [Jal callee] 
    ) in

    let caller_epilogue(args: Ast.exp list): inst list = (
      (* pop actual args, reset sp *)
      let arg_count = List.length args in
      [Add(R29, R29, Immed(Word32.fromInt (4*arg_count)))]
    ) in

    let rec compile_exp ((e,_):Ast.exp) : inst list = 
    match e with
        Int(i) -> [Li(R2, Word32.fromInt i)]
        | Var(v) -> (
            (* print_string v;
            print_int (1); *)
            let v_offset = Hashtbl.find (offset_table) v in
            if (v_offset > 0) then [Lw(R2,R30,Word32.fromInt (4*v_offset))]
            else [Lw(R2,R30,Word32.fromInt (4*(-1+v_offset)))])
        | Binop(e1, b, e2) -> (
            (* let t = new_temp()
            in ( *)
            [Add(R3, R0, Immed(Word32.fromInt 4)); Sub(R29, R29, R3)] @ (*allocate stack space for temp*)
            (compile_exp e1) @ [Sw(R2,R29,Word32.fromInt (0)) (*push temp*)]
            @(compile_exp e2) @ [Lw(R3,R29,Word32.fromInt (0)); Add(R29, R29, Immed(Word32.fromInt 4))(*pop temp*)]
            @(match b with
                Plus -> [Add(R2,R2,Reg R3)]
                | Minus -> [Sub(R2,R3,R2)]
                | Times -> [Mul(R2,R2,R3)]
                | Div -> [Div(R2,R3,R2)]
                | Eq -> [Seq(R2,R2,R3)]
                | Neq -> [Sne(R2,R2,R3)]
                | Lt -> [Slt(R2,R3,Reg(R2))]
                | Lte -> [Sle(R2,R3,R2)]
                | Gt -> [Sgt(R2,R3,R2)]
                | Gte -> [Sge(R2,R3,R2)]
            ))
        | Not(e) -> (compile_exp e) @ [Seq(R2,R2,R3)]                    
        | And(e1, e2) -> (
            (* let t = new_temp()
            in ( *)
            [Add(R3, R0, Immed(Word32.fromInt 4)); Sub(R29, R29, R3)] @ (*allocate stack space for temp*)
            (compile_exp e1) @ [Sw(R2,R29,Word32.fromInt (0)) (*push temp*)]
            @(compile_exp e2) @ [Lw(R3,R29,Word32.fromInt (0)); Add(R29, R29, Immed(Word32.fromInt 4))(*pop temp*)]
            @ [And(R2,R2,Reg R3)]
            )              
        | Or(e1, e2) -> (
            (* let t = new_temp()
            in ( *)
            [Add(R3, R0, Immed(Word32.fromInt 4)); Sub(R29, R29, R3)] @ (*allocate stack space for temp*)
            (compile_exp e1) @ [Sw(R2,R29,Word32.fromInt (0)) (*push temp*)]
            @(compile_exp e2) @ [Lw(R3,R29,Word32.fromInt (0)); Add(R29, R29, Immed(Word32.fromInt 4))(*pop temp*)]
            @ [Or(R2,R2,Reg R3); Li(R3, Word32.fromInt 0); Sgt(R2,R2,R3)]
            )                 
        (* | Assign(v, e) when v="b"-> (compile_exp e) @ [La(R3,"z"); Sw(R2,R3,Word32.fromInt 0)] *)
        | Assign(v, e)-> (
            let v_offset = Hashtbl.find (offset_table) v in
            (compile_exp e) @ (if (v_offset > 0) then [Sw(R2,R30,Word32.fromInt (4*(v_offset)))]
            else [Sw(R2,R30,Word32.fromInt (4*(-1+v_offset)))])
          )
        | Call(fn_name, fn_args) -> (caller_prologue fn_name fn_args) @ (caller_epilogue fn_args)
    in( 
    match s with
        | Exp(exp) ->  (compile_exp exp)                   
        | Seq(stmt1, stmt2) -> ((compile_stmt stmt1 offset_table)@(compile_stmt stmt2 offset_table)) 
        | If(exp, stmt1, stmt2) -> (
            let else_l = new_label() in
            let end_l = new_label() in
            (compile_exp exp) @ [Beq(R2,R0,else_l)] @
            (compile_stmt stmt1 offset_table) @ [J(end_l);Label(else_l)] @
            (compile_stmt stmt2 offset_table) @ [Label(end_l)]
            )
        | While(exp, stmt) -> (
            let test_l = new_label() in
            let top_l = new_label() in
            [J(test_l); Label(top_l)] @
            (compile_stmt stmt offset_table) @
            [Label(test_l)] @
            (compile_exp exp) @
            [Bne(R2,R0,top_l)]
            )
        | For(exp1, exp2, exp3, stmt) -> compile_stmt (Seq((Exp exp1, 0),(While(exp2,(Seq(stmt,(Exp exp3, 0)), 0)), 0)), 0) offset_table
        | Return(exp) -> (compile_exp exp) @ [Sub(R4, R2, R0)] (*also copy return value to a0*)
        | Let(v, exp, stmt) -> (compile_exp (Assign(v, exp),0)) @ (compile_stmt stmt offset_table)
    )

let callee_prologue (fn: Ast.funcsig) = (
  (* print_string "hello from callee prologue "; *)
  let _ = reset() in
  let offset_table = new_offset_table() in
  let offset_table = set_args_offset fn.args 1 offset_table in 
  let offset_table = (collect_vars_count fn.body offset_table) in
  let stack_size = 4 * ( 2 + !var_count) in
      (* Printf.printf "%d " !var_count;
      Printf.printf "%d " (Hashtbl.length (offset_table)); *)
      (* Printf.printf "%d " (Hashtbl.find (offset_table) "x");
      Printf.printf "%d " (Hashtbl.find (offset_table) "y"); *)
    (* create fn label, set new sp, save fp in temp R3, set new fp, save ra, save fp*)
      ([Label(fn.name); Add(R3, R0, Immed(Word32.fromInt stack_size)); Sub(R29, R29, R3); Sub(R3, R30, R0);
      Add(R30, R29, Immed(Word32.fromInt (stack_size-4)));
      Sw(R31, R30, Word32.fromInt 0); (*skipping saved registers*)
      Sw(R3, R30, Word32.fromInt (-4));
      ], offset_table)
)

let callee_epilogue (): inst list = (
  (* reset sp, ra, fp, jump to ra *)
  [Add(R29, R30, Immed(Word32.fromInt 4)); Lw(R31, R30, Word32.fromInt 0); Lw(R30, R30, Word32.fromInt (-4))](*; J("printInt")]*)
)

let rec compile (p : Ast.program) : result = 
    (* print_string "hello1"; *)
    let rec compile_fn (p : Ast.program) =
      (match p with
      | [] -> []
      | Fn(p_hd) :: p_tl -> 
            let (callee_p, offset_table) = (callee_prologue p_hd) in (
            (callee_p) @ (compile_stmt p_hd.body offset_table) @ (callee_epilogue()) @ (compile_fn p_tl))
      ) in
    { code = compile_fn p; data = [] }


let result2string (res:result) : string = 
    let code = res.code in
    let data = res.data in
    let strs = List.map (fun x -> (Mips.inst2string x) ^ "\n") code in
    let vaR8decl x = x ^ ":\t.word 0\n" in
    let readfile f =
      let stream = open_in f in
      let size = in_channel_length stream in
      let text = Bytes.create size in
      let _ = really_input stream text 0 size in
		  let _ = close_in stream in 
      text in
	  let debugcode = readfile "print.asm" in
	    "\t.text\n" ^
	    "\t.align\t2\n" ^
	    "\t.globl main\n" ^
	    (String.concat "" strs) ^
	    "\n\n" ^
	    "\t.data\n" ^
	    "\t.align 0\n"^
	    (String.concat "" (List.map vaR8decl data)) ^
	    "\n" ^
	    Bytes.to_string debugcode
