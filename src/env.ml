module SMap = Map.Make(String)

(*
   empty : 'a t
   val mem : key -> 'a t -> bool
   val add : key -> 'a -> 'a t -> 'a t
   val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
   val find_opt : key -> 'a t -> 'a option
*)
