(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Term : sig

  type t = Var of string | Const of Domain.t [@@deriving compare, sexp_of, hash]

  type comparator_witness

  val unvar: t -> string

  val comparator: (t, comparator_witness) Comparator.t

  val fv_list: t list -> t list

  val equal: t -> t -> bool

  val to_string: t -> string

  val list_to_string: t list -> string

end

module Sig : sig

  type props = { arity: int; ntconsts: (string * Domain.tt) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  val table: (string, props) Hashtbl.t

  val add: string -> (string * Domain.tt) list -> unit

  val print_table: unit -> unit

end

val check_terms: string -> Term.t list -> Term.t list
