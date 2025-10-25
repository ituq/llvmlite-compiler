(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86
open Asm

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be represented
   in 64 bit. This greatly simplifies code generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  fun (src: Ll.operand) -> match src with
    |Null -> (Movq, [(Imm (Lit 0L)); dest])
    |Const x -> (Movq,[(Imm (Lit x)); dest])
    |Gid name -> let mangled_name = Platform.mangle name in (Leaq, [(Ind3 (Lbl mangled_name , Rip)); dest ])
    |Id _uid -> let address = lookup ctxt.layout _uid in (Movq, [address; dest])



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)




(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int = match t with
  | Void -> 0
  | I1 -> 8
  | I8 -> 0
  | I64 -> 8
  | Ptr _ -> 8
  | Struct [] -> 0
  | Struct (t::tl) -> (size_ty tdecls t) + (size_ty tdecls (Struct tl))
  | Array (i, t) -> (size_ty tdecls t) * i
  | Fun _ -> 0
  | Namedt lbl -> size_ty tdecls (lookup tdecls lbl)




(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
failwith "compile_gep not implemented"

let x86operand_of_lloperand (op:Ll.operand) (ctxt:ctxt) : X86.operand = match op with
  | Null -> Imm (Lit 0L)
  | Const x -> Imm (Lit x)
  | Gid name -> Ind3 (Lbl (Platform.mangle name), Rip)
  | Id uid -> lookup ctxt.layout uid


(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
(*---------------------------------------------------------
----------------------HELPER FUNCTIONS---------------------
----------------------------------------------------------*)
  let move_op_to_register (src:Ll.operand) (dest:reg) = compile_operand ctxt (Reg dest) src in
(*----------------------------------------------------------*)
  let write_to_uid (src:X86.operand) (dest:uid): X86.ins list = match src with
    | Ind3 _ -> [(Movq, [src; ~%Rax]); (Movq, [~%Rax; (lookup ctxt.layout dest)])]
    | _ -> [(Movq, [src; (lookup ctxt.layout dest)])] in
(*----------------------------------------------------------*)

  let write_ptr_to_rax (ptr:Ll.operand): X86.ins = match ptr with
    |Null -> (Movq, [(Imm (Lit 0L)); Reg Rax])
    |Const x -> (Movq,[(Imm (Lit x)); Reg Rax])
    |Gid name -> let mangled_name = Platform.mangle name in (Leaq, [(Ind3 (Lbl mangled_name , Rip)); Reg Rax])
    |Id _uid -> let address = lookup ctxt.layout _uid in (Movq, [address;Reg Rax])
  in
(*----------------------------------------------------------*)
  let bop_to_opcode (b : Ll.bop) : X86.opcode =
    match b with
    | Ll.Add  -> X86.Addq
    | Ll.Sub  -> X86.Subq
    | Ll.Mul  -> X86.Imulq
    | Ll.Shl  -> X86.Shlq
    | Ll.Lshr -> X86.Shrq
    | Ll.Ashr -> X86.Sarq
    | Ll.And  -> X86.Andq
    | Ll.Or   -> X86.Orq
    | Ll.Xor  -> X86.Xorq in
(*----------------------------------------------------------*)
  let compile_binary_operation (op:bop) (typ:ty) (op1:Ll.operand) (op2:Ll.operand):X86.ins list =
      let instr1 = move_op_to_register op1 Rax in
      let isntr2 = move_op_to_register op2 Rcx in
      let instr3 = (bop_to_opcode op, [Reg Rcx; Reg Rax]) in
      let instr4 = write_to_uid (Reg Rax) uid in
      [instr1; isntr2; instr3]@instr4 in
  (*----------------------------------------------------------*)
  let write_bytes_to_x87_op (dest:X86.operand) (ty:ty)=
    (*src pointer is always rax*)
    let n =Int64.of_int @@ size_ty ctxt.tdecls ty in
    let range x = List.init (x + 1) (fun i -> i) in
    (* Example: range 5 returns [0; 1; 2; 3; 4; 5] *)
    (Movq,[dest; ~%Rcx]):: (List.flatten @@ List.map (fun i-> [(Movq,[Ind3 (Lit (Int64.of_int i), Rax); ~%Rcx]); (Incq,[~%Rcx]);(Incq,[~%Rax])]) (range (Int64.to_int n)))
  in
(*----------------------------------------------------------*)
  let call_helper (fun_ptr:Ll.operand) (all_args:(Ll.ty * Ll.operand) list):ins list =
   let rec save_args (regs: reg list) (args:(Ll.ty * Ll.operand) list):ins list = match (regs, args) with
     | (_, []) -> []
     | (next_reg::rest_regs, (_, next_arg)::rest_args) -> [move_op_to_register next_arg next_reg] @ save_args rest_regs rest_args
     | ([], (_, next_arg)::rest_args) -> save_args [] rest_args @ [(Pushq, [x86operand_of_lloperand next_arg ctxt])] in
   let fun_call = match fun_ptr with
     | Gid id -> [(Callq, [Imm (Lbl (Platform.mangle id))])]
     (*| Id id -> [(Callq, [lookup ctxt.layout id])]*)
     | Id _ -> failwith "Function pointer is local id in call"
     | _ -> failwith "Invalid llvm function operand in call" in
   let clean_stack = if List.length all_args > 6 then [(Addq, [Imm (Lit (Int64.mul (Int64.of_int ((List.length all_args)-6)) 8L)); Reg Rsp])] else [] in
   (save_args [Rdi; Rsi; Rdx; Rcx; R08; R09] all_args) @ fun_call @ clean_stack
  in
  (*---------------------------------------------------------
  ----------------------MAIN BODY----------------------------
  ----------------------------------------------------------*)
  match i with
  | Binop (op, typ, op1, op2) -> compile_binary_operation op typ op1 op2
  | Icmp (condition, ty, a, b)->
    let a_x86, b_x86 = x86operand_of_lloperand a ctxt, x86operand_of_lloperand b ctxt in
    let conditon_x86 = compile_cnd condition in
    let dest = lookup ctxt.layout uid in
    [(Movq,[a_x86; Reg Rax]); (Cmpq, [b_x86;Reg Rax]); (Movq, [Imm (Lit 0L); Reg Rax]); (Set conditon_x86, [Reg Rax]); (Movq, [Reg Rax; dest])]
  | Load (ty, ptr) -> [move_op_to_register ptr Rax; (Movq, [Ind3 (Lit 0L, Rax); ~%Rcx])]@(write_to_uid (~%Rcx) uid) (*only 64bit types and no type checks*)
  | Store (ty, src, ptr) -> [move_op_to_register src Rax; move_op_to_register ptr Rcx; (Movq, [~%Rax; Ind3 (Lit 0L, Rcx)])] (*only 64bit types and no type checks*)
  | Alloca typ -> [(Subq, [Imm (Lit (Int64.of_int (size_ty ctxt.tdecls typ))); ~%Rsp])]@(write_to_uid ~%Rsp uid)
  | Call (Void, fun_ptr, args) -> call_helper fun_ptr args
  | Call (_, fun_ptr, args) -> (call_helper fun_ptr args) @ (write_to_uid (~%Rax) uid) (*doesnt handel/check for invalid functions/return types*)
  | Bitcast (_, op, _) -> write_to_uid (x86operand_of_lloperand op ctxt) uid
  | _ -> failwith "compile_insn not implemented"



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let stack_cleanup_code= [(Movq , [~%Rbp; ~%Rsp]); (Popq, [~%Rbp])] in
  match t with
  | Br lbl -> [(Jmp, [Imm (Lbl (mk_lbl fn lbl))])]
  | Cbr (op, taken, not_taken) -> [(Cmpq, [Imm (Lit 1L); x86operand_of_lloperand op ctxt]); (J Eq, [Imm (Lbl (mk_lbl fn taken))]); (Jmp, [Imm (Lbl (mk_lbl fn not_taken))])]
  | Ret (Void,_) -> stack_cleanup_code@[ (Retq, [])]
  | Ret (_,Some op) -> [(Movq, [x86operand_of_lloperand op ctxt ; ~%Rax])] @ stack_cleanup_code @ [(Retq,[])]
  | _ -> failwith "llvm terminator not implemented"


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  let insns = List.flatten (List.map (compile_insn ctxt) blk.insns) in
  let term  = compile_terminator fn ctxt (snd blk.term) in
  insns @ term

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : X86.operand = match n with
  | 0 -> ~%Rdi
  | 1 -> ~%Rsi
  | 2 -> ~%Rdx
  | 3 -> ~%Rcx
  | 4 -> ~%R08
  | 5 -> ~%R09
  | _ -> Ind3 (Lit (Int64.mul (Int64.of_int (n-4)) 8L), Rbp) (*Nicht mehr wie in den slides weil dort 1-indexing genutz wird, wir aber alles mit 0-indexing geschrieben haben*)


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)


let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let insn_assigns (uid, insn) = match insn with
    | Store _ -> false
    | Call (Void, _, _) -> false
    | _ -> true
  in
  let uids_of_block b = List.map fst (List.filter insn_assigns b.insns) in
  let uids_of_initial_block = uids_of_block block in
  let uids_of_labelled_blocks = (List.flatten (List.map uids_of_block (List.map snd lbled_blocks))) in
  let all_uids = args @ uids_of_initial_block @ uids_of_labelled_blocks in
  List.mapi (fun i uid -> let offset = Int64.mul (Int64.neg (Int64.of_int (i + 1))) 8L  in
  ( uid, Ind3( Lit offset,Rbp))) all_uids


(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  let arg_uid = stack_layout f_param f_cfg in
  (*----------------------------------------------------------*)
  let write_to_uid (src:X86.operand) (dest:uid): X86.ins list = match src with
      | Ind3 _ -> [(Movq, [src; ~%Rax]); (Movq, [~%Rax; (lookup arg_uid dest)])]
      | _ -> [(Movq, [src; (lookup arg_uid dest)])] in
  (*----------------------------------------------------------*)
  let mover_ins =  List.flatten (List.mapi (fun i uid -> write_to_uid (arg_loc i) uid) f_param) in
  (*----------------------------------------------------------*)
  let aligned_bytes = Int64.mul (Int64.div (Int64.add ( Int64.mul (Int64.of_int (List.length arg_uid)) 8L) 15L) 16L) 16L in
  let prologue = [(Pushq, [~%Rbp]); (Movq , [~%Rsp; ~%Rbp]); (Subq, [Imm (Lit aligned_bytes); ~%Rsp])] in
  let context =  { tdecls = tdecls ; layout = arg_uid } in
  let fold_block (l:elem list) ((block_name,block): lbl*block)= l @ [(compile_lbl_block name block_name context block)] in
  Asm.gtext name (prologue@mover_ins@(compile_block name context (fst f_cfg))) :: List.fold_left  fold_block [] (snd f_cfg)




(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
