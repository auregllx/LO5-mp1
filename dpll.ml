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

exception Not_Found

(*
   simplifie : int -> int list list -> int list list option
   Simplifie les clauses en éliminant les littéraux inutiles.
*)


let rec simplifie_clause l clause = 
  (* Si l apparait dans la clause alors on renvoie [] *)
  if List.mem l clause then [] 
  else 
    match clause with 
    |[] -> [] 
    |[litt] when litt = -l -> [0]
    (* Si -l apparait alors on le supprime de clause *)
    |hd :: tl when hd = -l -> simplifie_clause l tl 
    (* Sinon on continue à parcourir la clause *)
    |hd :: tl -> hd :: (simplifie_clause l tl)
;;

let rec simplifie l clauses = 
  match clauses with 
  |[] -> [] 
  |hd :: tl -> 
    match simplifie_clause l hd with 
    (* Si clause est vide car l était dedans nous ne l'ajoutons pas à la nouvelle liste de clauses *)
    |[] -> simplifie l tl
    |[0] -> [] :: simplifie l tl
    (* Sinon on l'ajoute à la nouvelle liste de clauses *)
    |clause -> clause :: (simplifie l tl)
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
(* let () = print_modele (solveur_split systeme []) 
let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)





(* pur : int list list -> int option
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception 'Not_Found' *)

let rec pur clauses =
  (* Fonction auxillaire qui verifie si un element l apparait dans une liste de liste *)
  let rec contains list l = 
    match list with 
    |[] -> false
    |hd :: tl -> if mem l hd then true else contains tl l
  in
  match clauses with
  (* Aucune clause, on lève une exception Not_Found *)
  |[] -> raise Not_Found
  |clause :: tl ->
    match clause with 
    |[] -> pur tl (* Si la clause est vide, on passe à la suivante *)
    |litteral :: next -> 
      (* Vérifie si la négation du littéral courant n'apparaît pas dans les clauses restantes (tl) *)
      let is_negation_not_present = not (contains tl (-litteral)) in
      (* Vérifie si la négation du littéral courant n'apparaît pas dans la clause courante *)
      let is_negation_not_in_clause = not (List.mem (-litteral) clause) in
      (* On renvoie le littéral pur trouvé *)
      if is_negation_not_present && is_negation_not_in_clause then litteral  
      (* Sinon on continue la recherche dans les clauses restantes *)
      else pur (next :: tl)
;;



(* unitaire : int list list -> int option
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

let rec unitaire clauses = 
  match clauses with 
  |[] -> raise Not_Found (* Aucune clause, on lève une exception Not_Found *)
  |clause :: tl 
    -> match clause with 
    |[litt] -> litt (* Une clause unitaire contenant un seul littéral, on renvoie ce littéral *)
    |_ -> unitaire tl (* La clause n'est pas unitaire, on continue la recherche dans les clauses restantes *)
;;


(* solveur_dpll_rec : int list list -> int list -> int list option 
  Retourne :
   - Some interpretation : Si la formule est satisfiable et l'interprétation est la solution.
   - None : Si la formule est insatisfiable. *)

let rec solveur_dpll_rec clauses interpretation =
  match clauses with
  | [] -> Some interpretation  (* Toutes les clauses sont satisfaites, renvoyer l'interprétation *)
  | clause :: tl ->
    if List.mem [] clauses then
      None  (* Une clause est vide, la formule est insatisfiable *)
    else
      try
        let unit_literal = unitaire clauses in
        if 
          List.mem [-unit_literal] clauses then None 
        else 
          let simplified_clauses = simplifie unit_literal clauses in
          let new_interpretation = unit_literal :: interpretation in
          solveur_dpll_rec simplified_clauses new_interpretation
      with
      | Not_found ->
        try
          let pure_literal = pur clauses in
          if 
            List.mem [-pure_literal] clauses then None
          else 
            let simplified_clauses = simplifie pure_literal clauses in
            let new_interpretation = pure_literal :: interpretation in
            solveur_dpll_rec simplified_clauses new_interpretation
        with
        |Not_found ->
          let branche = solveur_split clauses interpretation in
          match branche with
          | None -> None  (* Aucune branche n'a abouti, la formule est insatisfiable *)
          | Some new_interpretation ->
            let l = hd new_interpretation in
            if 
              List.mem [-l] clauses then None
            else 
              let simplified_clauses = simplifie l clauses in
              solveur_dpll_rec simplified_clauses (l :: interpretation)
;;


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])