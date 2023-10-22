(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
   let rec simplifie l clauses =

    let rec simplifie_clause clause =
      match clause with
      | [] -> []  (* Clause vide, on la supprime *)
      | litteral :: tl when litteral = l -> []  (* Supprimer la clause si l'apparaît *)
      | litteral :: tl when litteral = (-l) -> simplifie_clause tl  (* Supprimer le littéral -l *)
      | litteral :: tl -> litteral :: simplifie_clause tl
    in
  
    match clauses with
    | [] -> []
    | clause :: tl ->
      let clause_simplifiee = simplifie_clause clause in
      if clause_simplifiee <> [] then (* Si la clause courant n'est pas vide après simplification *)
        clause_simplifiee :: simplifie l tl
      else
        simplifie l tl
  ;;

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)


exception Not_found


(* pur : int list list -> int option
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception 'Not_Found' *)

(* Fonction auxillaire qui verifie si un litteral est dans une clause *)
let rec contains list l = 
  match list with 
  |[] -> false
  |hd :: tl -> if List.mem l hd then true else contains tl l
;;



let rec pur clauses =
  (* à compléter *)
  match clauses with 
  |[] -> raise Not_found (* Si il n'y a aucune clauses *)
  |clause :: tl ->
    match clause with 
    |[] -> pur tl (* Si clause vide, on passe à la suivante *)
    |litteral :: next -> 
      if not(contains clauses (-litteral)) then litteral (* Si le négatif du littéral courant n'apparait pas on le renvoie *)
      else pur (next :: tl) 
;;

(* unitaire : int list list -> int option
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)



let unitaire clauses =
  (* à compléter *)
  let unit_clauses = List.filter (fun l -> List.length l = 1) clauses in 
  match unit_clauses with 
  |[] -> raise Not_found (* Aucune clause unitaire *)
  |unit_clause :: tl -> List.hd unit_clause (* On renvoie le litéral associé à la première clause unitiaire trouvée *)
;;

(* solveur_dpll_rec : int list list -> int list -> int list option *)
(* let rec solveur_dpll_rec clauses interpretation =
  None *)

let solveur_dpll_rec clauses interpretation = 
  let rec solveur_dpll cls interpretation = 
    if cls = [] then Some interpretation (* Si clauses est vide *)
    else if List.mem [] cls then None (* Si l'une des clauses est vide alors,  il n'y a aucune interprétation *)
    else 
      try (* On cherche de clauses unitaires *)
        let unit_litteral = unitaire cls in
        let simplified_clauses = simplifie unit_litteral cls in 
        solveur_dpll simplified_clauses (unit_litteral :: interpretation)
      with
        | Not_found -> 
          try (*Sinon, nous cherchons un littéral pur *)
            let pur_litteral = pur cls in
            let simplified_clauses = simplifie pur_litteral cls in
            solveur_dpll simplified_clauses (pur_litteral :: interpretation)
          with 
            |Not_found ->  (* Sinon nous cherchons un littéral par lequel la clause peut être satisfiable *)
            let l = hd (hd cls) in
            let branche = solveur_dpll (simplifie l cls) (l::interpretation) in
            match branche with
            | None -> solveur_dpll (simplifie (-l) cls) ((-l)::interpretation)
            | _    -> branche
    in
    solveur_dpll clauses interpretation
  

(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
