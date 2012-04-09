open Cil_types

(******************************************************************************)
open Graph;;

(* type d'un label (nom d'une fonction + nom d'une variable) et fonctions de
 * base *)
type label = Lbl of string * string;;
let compareLabel l1 l2 = match (l1, l2) with
        (Lbl(a, b), Lbl(c, d)) -> if (a > c) then 1 
                                  else if (a < c) then -1 
                                  else if (b > d) then 1 
                                  else if (b < d) then -1 
                                  else 0;; 
let equalLabel l1 l2 = match (l1, l2) with
        (Lbl(a, b), Lbl(c, d)) -> if (a = c) && (b = d) then true else false;;
let createLabel funcName varName = Lbl(funcName, varName);; 

(* type d'un vertex (label + liste de label + liste de constante) et fonctions de 
 * base *)
type solutions = Sol of label list * label list;;
let createSolutions labelsList constsList = Sol(labelsList, constsList);;

(* Pour creer un graphe avec ocamlGraph, on a besoin de creer un module
 * correspondant à la structure d'un sommet *)
module VertexMod = struct
        type t = label
        let compare = compareLabel
        let hash l = Hashtbl.hash l
        let equal = equalLabel
end;;

module G = Imperative.Digraph.Concrete(VertexMod);;

(* On utilise un dictionary pour que les noeuds soient accessibles à tous moments *)
module DictLabelType = struct
      type t = label
      let compare = compareLabel
end;;

module DictLabel = Map.Make(DictLabelType);;

(* on creer un graphe et un dictionary vides *)
let constraintGraph = G.create ();;

let labelDictionaryRef = (ref DictLabel.empty : solutions DictLabel.t ref);;

(* Ajoute dans le graphe et dans le dictionary un noeud paramêtré par un label,
 * une liste de labels et une liste de constante *)
let addNewConstraintVertex label labelsList constantsList graph vertDictRef = 
        let sortedLabelsList = List.sort (compare) labelsList in
        let sortedConstantsList = List.sort (compare) constantsList in
        let sol = createSolutions sortedLabelsList sortedConstantsList in
        let newVertex = G.V.create label in 
        G.add_vertex graph newVertex;
        vertDictRef := DictLabel.add label sol !vertDictRef;;

(* Ajoute dans le graphe un arc entre les noeuds désignés par label1 et label2.
 * Ces noeuds sont recupérés depuis le dictionary *)
let addConstraintEdge label1 label2 graph = 
        G.add_edge graph label1 label2;;

(* recupère la liste des labels des successeurs de label *)
let getSuccessor label graph = G.succ graph label;;

(* Merger des listes de string et des listes d'int *)
let rec rmDouble equal l = match l with
        []  -> []
      | [a] -> [a]
      | a::b::tail -> if equal a b then rmDouble equal (b::tail)
                      else a::(rmDouble equal (b::tail));;

let mergeLists l1 l2 =
        rmDouble (=) (List.merge (compare) l1 l2);;

(* Met à jour le dictionnaire en mergeant la nouvelle Sol avec l'ancienne Sol. *)
let updateVertexsolutions label labelsList constantsList vertDictRef =
        if DictLabel.mem label !vertDictRef then
                let Sol(a,b) = DictLabel.find label !vertDictRef in
                let rmVertDictRef = DictLabel.remove label !vertDictRef in
                let newLabelsList = mergeLists a labelsList in
                let newConstantsList = mergeLists b constantsList in
                let newSol = createSolutions newLabelsList newConstantsList in
                vertDictRef := DictLabel.add label newSol rmVertDictRef; true
        else false;;

(* Si le vertex existe deja on merge les solutions, sinon on le crée *)
let addConstraintVertex label labelsList constantsList graph vertDictRef =
        if updateVertexsolutions label labelsList constantsList vertDictRef then ()
        else addNewConstraintVertex label labelsList constantsList graph vertDictRef;;






(* Fonctions d'affichage des types *)
let labelToString label = let Lbl(a,b) = label in a^"_"^b;;

let rec labelListToString labelList = match labelList with
          [] -> ""
        | [head] -> (labelToString head)
        | head::tail -> (labelToString head)^", "^(labelListToString tail);;    

let vertexToString label sol = 
        let Sol(b,c) = sol in 
        (labelToString label)^"\\n{"^(labelListToString b)^"}\\n{"^(labelListToString c)^"}";;

let vertexLabelToString label = labelToString label;;

let vertexToStringFromDict label dict = 
        let sol = DictLabel.find label dict in
        vertexToString label sol;;

(* On veut utiliser le module Graphviz. On créer un module avec les bons
 * parametres *)
module type VERTEXDICT = sig
        val dict : solutions DictLabel.t
end;;

module DotGraph (D : VERTEXDICT) = struct
        type t = G.t
        module V = G.V
        module E = G.E
        let iter_vertex = G.iter_vertex
        let iter_edges_e = G.iter_edges_e
        let graph_attributes _ = []
        let default_vertex_attributes _ = [`Shape `Box]
        let vertex_name v = vertexLabelToString v
        let vertex_attributes v = [`Label (vertexToStringFromDict v D.dict)]
        let get_subgraph _ = None
        let default_edge_attributes _ = []
        let edge_attributes _ = []
end;;

let output_dot g ~file labelDictRefp = 
        let module DictModForDot = struct let dict = !labelDictRefp end in
        let module DotGraphMod = DotGraph(DictModForDot) in
        let module Dot = Graphviz.Dot(DotGraphMod) in
        let outc = open_out file in Dot.output_graph outc g;;

(* Types correspondant aux contraintes d'inclusion *)

type simpleConstraint =  C1 of label * label
                       | C2 of label * label
                       | C3 of label * label;;

type complexConstraint =  C4 of label * label
                        | C5 of label * label;;

(* On utilise un dictionary pour que les contraintes complexes soient
 * accessibles à tous moments.
 * La clé est le label du pointeur dereferencé. *)
let cplxConstDictRef = (ref DictLabel.empty : complexConstraint DictLabel.t ref);;

(* Algorithme de création du graphe *)
let rec createConstraintGraph graph simplConstList vertDictRef = match simplConstList with
          [] -> ()
        | (C1(a,b))::tail -> 
                        addConstraintVertex a [] [] graph vertDictRef;
                        addConstraintVertex b [] [] graph vertDictRef;
                        addConstraintEdge b a graph;
                        createConstraintGraph graph tail vertDictRef
        | (C2(a,b))::tail ->
                        addConstraintVertex a [b] [] graph vertDictRef;
                        createConstraintGraph graph tail vertDictRef
        | (C3(a,b))::tail ->
                        addConstraintVertex a [] [b] graph vertDictRef;
                        createConstraintGraph graph tail vertDictRef;;

(* Gestion de la WorkList *)
let createWorklist vertDict worklistRef =
        let f worklRef key _ = (worklRef := key::(!worklRef)) in 
        DictLabel.iter (f worklistRef) vertDict;;

let popNextLabelInWorklist worklistRef = match !worklistRef with 
          [] -> worklistRef := []; Lbl("","")
        | a::tail -> worklistRef := tail; a;;

let pushNextLabelInWorklist worklistRef label = match !worklistRef with
          [] -> worklistRef := [label]
        | a::tail -> if a = label then worklistRef := a::tail 
                     else worklistRef := label::a::tail;;

(* Tests *)

let cg = constraintGraph;;
let lD = labelDictionaryRef;;

(* Creation d'une liste de contrainte simple. Puis creation du graphe associé *)
let simplConstList = 
        let a = C1(Lbl("ta", "b"), Lbl("ta","c")) in
        let b = C1(Lbl("tb", "b"), Lbl("tb","c")) in
        let c = C1(Lbl("tc", "b"), Lbl("tc","c")) in
        let d = C1(Lbl("ta", "b"), Lbl("tb","c")) in
        let e = C1(Lbl("tb", "b"), Lbl("tc","c")) in
        let f = C2(Lbl("tb", "b"), Lbl("tc","c")) in
        let g = C2(Lbl("ta", "b"), Lbl("tb","c")) in
        let h = C3(Lbl("tb", "b"), Lbl("tb","3")) in
        let i = C3(Lbl("tc", "b"), Lbl("tb","1")) in
        [a; d; h; c; i; g; b; e; f];;
(******************************************************************************)

(* register your plug-in to access basic services *)
include Plugin.Register
  (struct
    let name = "pointer constraints"
    let shortname = "constraint"
    let help = "Make a temp.dot file with the graph"
  end)

(* les methodes de cette classe sont utilisées pour faire du debug *)
class shared = object (self)

    method private print_position pos = "(" ^ pos.Lexing.pos_fname ^ " " ^ (string_of_int pos.Lexing.pos_lnum) ^ " " ^ (string_of_int pos.Lexing.pos_bol) ^ " " ^ (string_of_int pos.Lexing.pos_cnum) ^ ")"

(*
    method private print_location (pos_a, pos_b) = "[" ^ (self#print_position pos_a) ^ "," ^ (self#print_position pos_b) ^ "]"
*)
  method private print_location (_, _) = ""

  method private print_type t = match t with
      | TVoid _ -> "void"
      | TInt _ -> "int"
      | TFloat _ -> "float"
      | TPtr _ -> "ptr"
      | TArray _ -> "array"
      | TFun _ -> "fun"
      | TNamed _ -> "named"
      | TComp _ -> "comp"
      | TEnum _ -> "enum"
      | TBuiltin_va_list _ -> "buildin_va_list"

    method private print_varinfo v = v.vname ^ " " ^ (self#print_type v.vtype)

    method private print_varinfo_list vl = 
      let rec print_varinfo_list_aux vlaux accu first = match vlaux with
        | [] -> accu ^ "]"
        | h::t -> print_varinfo_list_aux t (accu ^ (if first then "" else ",") ^ (self#print_varinfo h)) false
      in print_varinfo_list_aux vl "[" true

    method private print_fundec f = (self#print_varinfo f.svar) ^ " " ^ (self#print_varinfo_list f.sformals)

    method private print_glob_fun (f, _) = (self#print_fundec f)

    method private print_lhost lh = match lh with
      | Var vi -> self#print_varinfo vi
      | Mem e -> self#print_expr e

    method private is_lval_ptr (lh, _) = match lh with
      | Var _ -> false
      | Mem _ -> true

(*    method private print_offset o = match o with
      | NoOffset -> "nooffset"
      | Field _ -> "field"
      | Index _ -> "index"
*)
    method private print_offset _  = ""

    method private print_lval lv = let (lh, off) = lv in  "lval:[" ^ (self#print_lhost lh) ^ " " ^ (self#print_offset off) ^ "]"

    method private print_opt_lval olv = match olv with
      | None -> "none";
      | Some e -> (self#print_lval e);

    method private print_mem e = self#print_expr e
    
(*    method private print_varinfo v = *)

    method private print_unop u = match u with
      | Neg -> "-"
      | BNot -> "~"
      | LNot -> "!"

    method private print_binop b = match b with
     | PlusA -> "+"
     | PlusPI -> "p+i"
     | IndexPI -> "ip+i"
     | MinusA -> "-"
     | MinusPI -> "p-i"
     | MinusPP -> "ip-i"
     | Mult -> "*"
     | Div -> "/"
     | Mod -> "%"
     | Shiftlt -> "<<"
     | Shiftrt -> ">>"
     | Lt -> ">"
     | Gt -> ">"
     | Le -> "<="
     | Ge -> ">="
     | Eq -> "=="
     | Ne -> "!="
     | BAnd -> "&"
     | BXor -> "^"
     | BOr -> "|"
     | LAnd -> "&&"
     | LOr -> "||"

    method private print_caste (t, e) = "[cast (" ^ (self#print_type t) ^ ") ( " ^ (self#print_expr e) ^ ")]"

    method private print_expr_aux expr = match expr.enode with
      | Const _ -> "const"
      | Lval lv -> (self#print_lval lv)
      | SizeOf t -> "sizeof(" ^ (self#print_type t) ^ ")"
      | SizeOfE e -> "sizeof(" ^ (self#print_expr e) ^ ")"
      | SizeOfStr s -> "sizeof(" ^ s ^ ")"
      | AlignOf t -> "__alignof_(" ^ (self#print_type t) ^ ")"
      | AlignOfE e -> "__alignof_(" ^ (self#print_expr e) ^ ")"
      | UnOp (u, e, t) -> "unop([" ^ (self#print_unop u) ^ "," ^ (self#print_expr e) ^ "]:" ^ (self#print_type t) ^ ")"
      | BinOp (b, e1, e2, t) -> "binop([" ^ (self#print_binop b) ^ "," ^ (self#print_expr e1) ^ "," ^ (self#print_expr e2) ^ "]:" ^ (self#print_type t) ^ ")"
      | CastE (t, e) -> self#print_caste (t, e)
      | AddrOf lv -> "addrof(" ^ (self#print_lval lv) ^ ")"
      | StartOf lv -> "addrof(" ^ (self#print_lval lv) ^ ")"
      | Info (e, _) -> "info("^ (self#print_expr e) ^ ")"

    method private print_expr expr = "expr:[" ^ (self#print_expr_aux expr) ^ "]"

    method private print_opt_exp exp = match exp with
      | None -> "none";
      | Some e -> (self#print_expr e);

    method private print_expr_list exprl = 
      let rec print_expr_list_aux exprlaux accu first = match exprlaux with
        | [] -> accu ^ "]"
        | h::t -> print_expr_list_aux t (accu ^ (if first then "" else ",") ^ (self#print_expr h)) false
      in print_expr_list_aux exprl "[" true

   method private print_instr instr = match instr with 
      | Set (lv, e, loc) -> "set[" ^ (self#print_lval lv) ^ "," ^ (self#print_expr e) ^ (self#print_location loc) ^ "]"
      | Call (lv, e, el, l) -> "call [" ^ (self#print_opt_lval lv) ^ "] [" ^ (self#print_expr e) ^ "] [" ^ (self#print_expr_list el) ^ "] [" ^ (self#print_location l) ^ "]"
      | Asm _ -> "asm"
      | Skip l -> "skip " ^ (self#print_location l)
      | Code_annot _ -> "code annot"

    method private print_goto _ = "goto"

    method private print_break b = self#print_location b

    method private print_continue c = self#print_location c

    method private print_if (e, _, _, l) = (self#print_expr e) ^ (self#print_location l)
end

let uniqueId = ref 0
(* Génère un entier unique *)
let unique () = let inc = !uniqueId + 1 in uniqueId := inc; !uniqueId

(* terme de droite d'une contrainte, le terme de gauche est forcement une lval (string, string, TPtr, nb_deref) *)
type myexpr = MyConst of (string * int) | MyAddrOf of (string * string * typ * int) | MyPointer of (string * string * typ * int)

(* Affiche n étoiles *)
let rec p_stars n = if (n != 0) then "*" ^ (p_stars (n - 1)) else ""

(* debug *)
let dump_myexpr anexpr =
  match anexpr with
    | MyConst (s, i) -> s ^ (string_of_int i)
    | MyAddrOf (f, v, _, _) -> "&" ^ f ^ "$" ^ v
    | MyPointer (f, s, _, i) -> (p_stars i) ^ f ^ "$" ^ s

exception MyException

(* Cette fonction calcule le graphe de constrainte à partir de l'ast et génère un fichier dot qui représente ce graphe *)
let mk_graph () =
  let myconstraints = ref [] in
  let globals_visitor = object (self)
    (* visit the AST in place by inheritance *)
    inherit shared 
    inherit Visitor.frama_c_inplace

      (* surcharge de vglob_aux pour aller dans chaque fonction *)
      method vglob_aux g = match g with
        | GFun (f, _) -> (* result "visit %s" (self#print_fundec f) ; *)
          (* stocke le nom de la fonction courante *)
          let function_name = f.svar.vname in 
            (* visitor pour créer les contraintes depuis les stmt *)
            let function_visitor = object (this)
              (* visit the AST in place by inheritance *)
              inherit shared
              inherit Visitor.frama_c_inplace
              
              (* Retourne le type d'une lval : depuis le varinfo si Var, reccursivement à travers l'exp de Mem
               * Ne fonctionne que pour les variables "simples" par exemple raise une exception sur *(a + 2)
               *)
              method private find_type_rec l = 
                let rec find_type_rec_aux lval accu = 
                  let (lhost, _) = lval in
                    match lhost with
                      | Var varinfo -> (function_name, varinfo.vname, varinfo.vtype, accu)
                      | Mem e -> (match e.enode with
                        | Lval lval1 -> find_type_rec_aux lval1 (accu + 1)
                        | _ ->  raise MyException)
                in find_type_rec_aux l 0

              (* Retourne une liste des myexpr associés à une exp *)
              method private calc_myexpr_list e =
                let rec print_expr_aux_aux expr =
                  match expr.enode with
                    | BinOp (_, e1, e2, _) -> let expr_node1 = print_expr_aux_aux e1 in let expr_node2 = print_expr_aux_aux e2 in expr_node1@expr_node2
                    | UnOp (_, e, _) -> print_expr_aux_aux e
                    | CastE (_, e) -> print_expr_aux_aux e
                    | Const _ -> [MyConst( function_name, unique ())]
                    | Lval lv -> let (aa1, aa2, bb, cc) = this#find_type_rec lv in 
                      (match bb with
                        | TPtr _ -> [MyPointer(aa1, aa2, bb, cc)]
                        | _ -> [MyConst(function_name, unique ())]
                      )
                    | AddrOf lv -> let (aa1, aa2, bb, cc) = this#find_type_rec lv in [MyAddrOf(aa1, aa2, bb, cc)]
                    | _ -> result "other expr"; []
                  in print_expr_aux_aux e

              method private mymerge l1 l2 =
                let rec myinsert item ll1 = 
                  match ll1 with 
                    | [] -> item::[]
                    | h::t -> if (h != item) then h::(myinsert item t) else ll1
                in
                  let rec mymerge_aux ll1 ll2 = 
                    match ll1 with
                      | [] -> ll2
                      | h::t -> mymerge_aux t (myinsert h ll2)
                  in mymerge_aux l1 l2

              (* Génère et ajoute des contraintes à la liste des contraintes *)
              method private mksetconstraint (lval, exp) = 
                let (a1, a2, b, c) = (this#find_type_rec lval) in 
                  match b with
                    | TPtr _ -> (* result "%s" (a ^ " ptr (" ^ (string_of_int c) ^ ")"); *)
                      let myexpr_list = (this#calc_myexpr_list exp) in
                        let rec putinconstraint anmyexpr_list = 
                          match anmyexpr_list with
                            | [] -> []
                            | h::t -> ((a1, a2, b, c), h)::(putinconstraint t)
                        in let myconstraint_list = putinconstraint myexpr_list in
                          myconstraints := (this#mymerge myconstraint_list (!myconstraints));
                      ()
                    | _ -> ()
                    
            method private mkfunctionconstraint (lval, exp, exp_list) = 
              let called_function = match exp.enode with
                | Lval lval -> let (lhost, _) = lval in (
                  match lhost with
                    | Var varinfo -> varinfo.vname
                    | _ -> "" )
                | _ -> ""
              in 
              let (a1, a2, b, c) = this#find_type_rec lval in 
                match b with
                  | TPtr _ -> (* result "%s" (a ^ " ptr (" ^ (string_of_int c) ^ ")"); *)
                    let rec calc_args_exp exp_args_list = 
                      match exp_args_list with
                        | [] -> []
                        | h::t -> (calc_args_exp t)@(this#calc_myexpr_list h)
                    in let myexprs_list = calc_args_exp exp_list in
                      let rec putinconstraint anmyexpr_list = 
                        match anmyexpr_list with
                          | [] -> [((a1, a2, b, c), MyPointer(called_function, "ret", b, 0))]
                          | h::t -> (match h with
                            | MyConst _ -> (putinconstraint t)
                            | MyAddrOf _ -> (putinconstraint t)
                            | MyPointer (_, zz, _, _) -> ((called_function, zz, b, c), h)::(putinconstraint t))
                      in let myconstraint_list = putinconstraint myexprs_list in
                        myconstraints := this#mymerge myconstraint_list (!myconstraints);
                    ()                         
                  | _ -> ()
            
            method private addconstraint instr =
              match instr with
                | Set (lval, exp, _) -> this#mksetconstraint (lval, exp)
                | Call (lval_option, exp, exp_list, _) -> (
                  match lval_option with
                    | None -> () (* self#mkprocconstraint (exp, exp_list) *)
                    | Some e -> this#mkfunctionconstraint (e, exp, exp_list))
                | _ -> ()
                
            method private mkreturnconstraint e = 
              let myexpr_list = (this#calc_myexpr_list e) in
                let rec putinconstraint anmyexpr_list = 
                  match anmyexpr_list with
                    | [] -> []
                    | h::t -> (match h with
                            | MyConst _ -> (putinconstraint t)
                            | MyAddrOf _ -> (putinconstraint t)
                            | MyPointer (_, _, b, c) -> ((function_name, "ret", b, c), h)::(putinconstraint t))
                in let myconstraint_list = putinconstraint myexpr_list in
                  myconstraints := this#mymerge myconstraint_list (!myconstraints);
                ()
              
            method private addreturnconstraint exp_option = 
              match exp_option with
                | None -> () (* self#mkprocconstraint (exp, exp_list) *)
                | Some e -> this#mkreturnconstraint e 
            
            method vstmt_aux s = match s.skind with
              | Instr i -> this#addconstraint i; Cil.DoChildren
              | Return (eo, _) -> this#addreturnconstraint eo; Cil.DoChildren
              | _ -> (* result " other"; *) Cil.DoChildren
          end
        in Visitor.visitFramacFunction function_visitor f ; Cil.DoChildren
      | _ -> Cil.DoChildren
  end
  
  in Visitor.visitFramacFile globals_visitor (Ast.get ()) ;
  let rec print_myconstraint_list cl =
    match cl with
      | [] -> ""
      | h::t -> let ((a1, a2 , _ , c), d) = h in (p_stars c) ^ a1 ^ "$" ^ a2 ^ "<" ^ (dump_myexpr d) ^ "|" ^ (print_myconstraint_list t)
  in result "%s" (print_myconstraint_list !myconstraints) ;
  let rec mk_simpl_constraint cst_lst = 
    match cst_lst with
      | [] -> []
      | ((a1, a2, _, c), d)::t ->
        (if (c != 0) 
          then mk_simpl_constraint t
          else (match d with
            | MyConst (s, i) -> C3(Lbl(a1, a2), Lbl(s, string_of_int i))::(mk_simpl_constraint t)
            | MyAddrOf (aa1, aa2, _, _) -> C2(Lbl(a1, a2), Lbl(aa1, aa2))::(mk_simpl_constraint t)
            | MyPointer (aa1, aa2, _, cc) ->
              (if (cc != 0)
                then mk_simpl_constraint t
                else C1(Lbl(a1, a2), Lbl(aa1, aa2))::(mk_simpl_constraint t))))
  in let simple_constraint_izzy = mk_simpl_constraint !myconstraints in 
    createConstraintGraph cg simple_constraint_izzy lD;
  output_dot cg "temp.dot" lD;
  ()

  (* Cette fonction affiche l'ast dans la console *)
  let print_ast () =
    let print_visitor = object (self)
    (* visit the AST in place by inheritance *)
      inherit shared 
      inherit Visitor.frama_c_inplace
      
      method vstmt_aux s = match s.skind with
      | Instr i -> result "instr %s" (self#print_instr i); Cil.DoChildren
      | Return (eo, _) -> result "return %s" (self#print_opt_exp eo); Cil.DoChildren
      | Goto _ -> result "goto"; Cil.DoChildren
      | Break _ -> result "break"; Cil.DoChildren
      | Continue _ -> result "%s" "continue"; Cil.DoChildren
      | If (e, b1, b2, l) -> result "%s" (self#print_if (e, b1, b2, l)); Cil.DoChildren
      | Switch _ -> result "%s" "switch"; Cil.DoChildren
      | Loop _ -> result "loop"; Cil.DoChildren
      | Block _ -> result "block"; Cil.DoChildren
      | UnspecifiedSequence _ -> result "unspecified sequence"; Cil.DoChildren
      | _ -> result "other stmt"; Cil.DoChildren
    end
    in Visitor.visitFramacFile print_visitor (Ast.get ()) ;
    ()

(* boolean option ‘-constraint’ initialized to [false] *)
module Enable =
  False(struct
    let option_name = "-constraint"
    let help = "output a tmp.dot constraints graph"
    let kind = `Correctness
  end)

(* boolean option ‘-printast’ initialized to [false] *)
module PrintEnable =
  False(struct
    let option_name = "-printast"
    let help = "output a text dump of the ast"
    let kind = `Correctness
  end)

(* Fonction enregistrée dans la Db des plugin *)  
let main () =
  (* compute ff the option is set *)
  if Enable.get () then begin
    mk_graph ();
    result "Done"
  end
  else if PrintEnable.get () then begin
    print_ast ();
    result "Done"
  end

(* execute your plug-in among the others *)
let () = Db.Main.extend main
