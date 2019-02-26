let size = 9

(** Intsets *)

type intset = Bitv.t
let empty = Bitv.create size false
let add s n =
  let s' = Bitv.copy s in
  Bitv.set s' n true;
  s'
let rm s n =
  let s' = Bitv.copy s in
  Bitv.set s' n false;
  s'
let iter_set f x = Bitv.iteri_true f x
let cardinal = Bitv.pop

(** Cow *)

type 'a cow = 'a array

let get x (i, j) = x.(i*size+j)
let set_mut x (i, j) v = x.(i*size+j) <- v
let set x (i, j) v = let a = Array.copy x in a.(i*size+j) <- v; a

(** Cells *)
  
let full_cell =
  let rec f i set =
    if i < 0 then set else f (i-1) (add set i)
  in
  f (size-1) empty

let singleton n = add empty n

(** Grid *)

type grid = intset cow

let pp fmt g =
  for i = 0 to size-1 do
    for j = 0 to size-1 do
      Bitv.iteri_true (fun i -> Format.pp_print_int fmt (i+1)) (get g (i, j));
      Format.fprintf fmt ",";
    done;
    Format.pp_print_newline fmt ();
  done
let print = Format.printf "%a@." pp

(* CORE ALGO START *)

let remove_line i0 j0 g n =
  for j = j0+1 to size - 1 do
    set_mut g (i0, j) (rm (get g (i0 , j)) n)
  done

let remove_column i0 j0 g n =
  for i = i0+1 to size - 1 do
    set_mut g (i , j0) (rm (get g (i , j0)) n)
  done

let remove_square i0 j0 g n =
  let pos_i = i0/3 in
  let pos_j = j0/3 in
  for i = 3*pos_i to 3*(pos_i+1) - 1 do
    for j = 3*pos_j to 3*(pos_j+1) - 1 do
      if not (i = i0 && j = j0) then
        set_mut g (i , j) (rm (get g (i , j)) n)
    done
  done

let is_valid g =
  Array.for_all (fun x -> cardinal x > 0) g

let is_solved g =
  Array.for_all (fun x -> cardinal x = 1) g

let next_pos (i, j) =
  if j < size - 1 then (i, j+1) else (i+1, 0)

let remove i j g n =
  remove_line i j g n;
  remove_column i j g n;
  remove_square i j g n;
  ()

let rec solve i j g =
  if is_solved g
  then print g
  else 
    let s = get g (i,j) in
    let new_i, new_j = next_pos (i,j) in
    let f n =
      let new_g = set g (i,j) (singleton n) in
      remove i j new_g n;
      if is_valid new_g
      then solve new_i new_j new_g
      else ()
    in
    iter_set f s

(* CORE ALGO END *)

let parse s =
  let g = Array.make (size*size) full_cell in
  for i = 0 to size-1 do
    for j = 0 to size-1 do
      let c = String.get s (i*size+j) in
      if c = '.' then ()
      else
        let n = (Char.code c - Char.code '0') in
        set_mut g (i,j) (singleton (n -1));
        remove i j g (n-1)
    done;
  done;
  g


(* From https://github.com/Gbury/mSAT/blob/master/tests/sudoku/sudoku.txt *)
let g = parse "12.3....435....1....4........54..2..6...7.........8.9...31..5.......9.7.....6...8"
  
let () = print g
let () = solve 0 0 g
