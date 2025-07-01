fun prn (str: string): unit = TextIO.output (TextIO.stdOut, str ^ "\n")
exception unimplemented of string
val max = Int.max

structure Result = struct
  datatype ('a, 'b) result = Ok of 'a | Err of 'b

  infix >>=
  fun (r: ('a, 'c) result) >>= (f: 'a -> ('b, 'c) result): ('b, 'c) result =
    case r of Ok x => f x | Err e => Err e
end

structure Type :> sig
  datatype t =
    FUN of (t vector) * t
  | SUM of t vector
  | PROD of t vector
  | PRIM of t * (t vector)
    (* TODO: uint? *)
  | LEVEL of int

  val pp: t -> string
  val result: t -> t
  val eq: t * t -> bool
  val level: t -> int
end = struct
  datatype t =
    FUN of (t vector) * t
  | SUM of t vector
  | PROD of t vector
  | PRIM of t * (t vector)
  | LEVEL of int


  fun pp_vec (v: t vector): string =
    let fun f (0, e, _) = pp e
          | f (_, e, acc) = acc ^ " " ^ (pp e)
    in (Vector.foldli f "" v)
    end

  and pp (t: t): string =
    case t of
      FUN (args, ret) => "(-> " ^ (pp_vec args) ^ " " ^ (pp ret) ^ ")"
    | SUM ss => "(sum " ^ (pp_vec ss) ^ ")"
    | PROD ps => raise unimplemented "Type.pp prod"
    | PRIM (p, ps) => raise unimplemented "Type.pp prim"
    | LEVEL l => "(Type " ^ (Int.toString l) ^ ")"

  fun result (FUN (_, r)) = r
    | result (PRIM (ty, _)) = ty
    | result r = r

  fun eq (l: t, r: t): bool =
    let
      fun vcheck (lv, rv) =
        let
          val llen = Vector.length lv
          val rlen = Vector.length rv
          fun f i =
            if i = llen then true
            else eq (Vector.sub (lv, i), Vector.sub (rv, i)) andalso f (i + 1)
        in llen = rlen andalso f 0
        end
    in case (l, r) of
      (FUN (la, lr), FUN (ra, rr)) =>
        Vector.length la = Vector.length ra andalso eq (lr, rr)
          andalso vcheck (la, ra)
    | (SUM ls, SUM rs) => vcheck (ls, rs)
    | (PROD lp, PROD rp) => vcheck (lp, rp)
      (* TODO: Just comparing on the holes isn't sufficient *)
    | (PRIM lp, PRIM rp) => raise unimplemented "Type.eq prim"
    | (PRIM lp, FUN (ra, rr)) => raise unimplemented "Type.eq prim/fun"
    | (FUN (la, lr), PRIM rp) => raise unimplemented "Type.eq fun/prim"
    | (LEVEL l, LEVEL r) => l = r
    | _ => false
    end

  fun vec_lvl (vs: t vector) = Vector.foldl (fn (t, m) => max (level t, m)) 0 vs
  and level (FUN (ts, t)) = max (level t, vec_lvl ts)
    | level (SUM ts) = vec_lvl ts
    | level (PROD ts) = vec_lvl ts
    | level (PRIM (t, ts)) = max (level t, vec_lvl ts)
    | level (LEVEL i) = i
end

structure Value :> sig
  datatype t =
    LAM of unit
  | PRIM of int
  | TYPE of Type.t

  val pp: t -> string
  val typeof: t -> Type.t
end = struct
  datatype t =
    LAM of unit
  | PRIM of int
  | TYPE of Type.t

  fun pp _ = raise unimplemented "Value.pp"
  fun typeof _ = raise unimplemented "Value.typeof"
end

signature Hashable = sig
  eqtype t
  val hash: t -> word
end

structure IntHasher: Hashable =
struct
  type t = int
  fun hash (i: int): word = Word.fromInt i
end

structure StringHasher: Hashable =
struct
  open Word
  infix << +
  type t = string
  fun hash (s: string): word =
    let fun f (c, h) = ((h << (Word.fromInt 5)) + h) + (Word.fromInt (ord c))
    in CharVector.foldl f (Word.fromInt 5381) s
    end
end

functor HashMap(
  structure H: Hashable
  type value
) = struct
  type key = H.t
  type t = { buf: (word * key * value) list array, len: int ref, cap: int ref }
  datatype ins_or_get = INSERT of t | GET of value

  fun calc_idx (k: key, sz: int): int =
    Word.toInt (Word.mod (H.hash k, Word.fromInt sz))
  fun get_idx (buf: t, k: key): int = calc_idx (k, !(#cap buf))

  fun empty () = { buf = Array.array (7, []), len = ref 0, cap = ref 7 }
  fun app (f: (word * key * value) -> unit) (tbl: t): unit =
    Array.app (fn ls => List.app f ls) (#buf tbl)
  fun fold (f: (word * key * value) * 'a -> 'a) (acc: 'a) (tbl: t): 'a =
    Array.foldl (fn (ls, acc) => List.foldl f acc ls) acc (#buf tbl)

  fun grow (tbl as { buf, len = ref len, cap = ref cap }: t): t =
    let
      val suggested_size = floor ((Real.fromInt cap) * 1.5)
      val newsz = if suggested_size > cap + 2 then suggested_size else cap * 2
      val newbuf = Array.array (newsz, [])
      fun f (tup as (word, key, value)): unit =
        let
          val idx = calc_idx (key, newsz)
          val bucket = Array.sub (newbuf, idx)
        in Array.update (newbuf, idx, tup :: bucket)
        end
      val () = app f tbl
    in { buf = newbuf, len = ref len, cap = ref newsz }
    end

  fun try_get
    (tbl as { buf, len = ref len, cap = ref cap }: t, k: key): value option
  = let
      val h = H.hash k
      fun f (_, SOME x) = SOME x
        | f ((h', k', v'), _) =
          if h <> h' orelse k <> k' then NONE else SOME v'
    in List.foldl f NONE (Array.sub (buf, get_idx (tbl, k)))
    end

  fun insert
    (tbl as { buf, len = ref len, cap = ref cap }: t, k: key, v: value): t
  = let
      val tbl' = if (Real.fromInt len) > 0.8 * (Real.fromInt cap)
        then grow tbl
        else tbl
      val idx = get_idx (tbl', k)
      fun f ([], ys) = (H.hash k, k, v) :: ys
        | f ((x as (h',k',v'))::xs, ys) =
          if k' = k then (h',k,v)::ys else f (xs, x::ys)
      val bucket = f (Array.sub (#buf tbl', idx), [])
    in (Array.update (#buf tbl', idx, bucket); #len tbl' := len + 1; tbl')
    end

  fun insertOrGet (tbl: t, k: key, v: value): ins_or_get =
    case try_get (tbl, k) of
      SOME v' => GET v'
    | NONE => INSERT (insert (tbl, k, v))
end

open Result
infix >>=

(*
 * Fundamentals
 * ============
 * claim    links an identifier and a type
 * alias    links an identifier and a value
 * prim     creates a new primitive value (also for pattern matching)
 * sum      creates a new sum type
 * prod     creates a new prod type
 * lambda   creates a new function
 * ->       create a new function type
 * =        equality ("unwrap" all the definitions)
 * :        bind a name at the type level to a parameter (with usage)
 * macro    introduces a type-less s-expr transformer
 * match    deconstruct a value
 *)

(* TODO: Consider refactoring this into a functor *)
structure Source = struct
  structure Mark = struct
    type t = { pos: int, line: int, col: int }

    fun new_line { pos = p, line = l, col = c }: t =
      { pos = p + 1, line = l + 1, col = 1 }
    fun advance { pos = p, line = l, col = c }: t =
      { pos = p + 1, line = l, col = c + 1 }
  end

  type token = int
  type t = {
    buf: string,
    point: Mark.t ref,
    marks: (string * Mark.t * token) list ref,
    next_tok: token ref
  }

  type slice = { start: Mark.t, finish: Mark.t }
  exception exc of string
  val succeed_no_start = "internal error: attempting to succeed at reading" ^
    " without having started to read anything"
  val fail_no_start = "internal error: attempting to fail at reading without" ^
    " having started to read anything"
  val big_line_pos = "internal error: attempting to convert pos to line and" ^
    " column when pos is pointing past the end of the buffer"
  val bad_token = "internal error: attempted to remove mark with invalid token"
  val bad_prev = "internal error: attempted to step back before start of buffer"

  fun point (buf: t): Mark.t = !(#point buf)
  fun prev_point (buf: t): Mark.t =
    let
      val { pos = p, line = l, col = c } = point buf
      fun find_ll (pos, len) =
        if pos = 0 then len
        else case String.sub (#buf buf, pos) of
            #"\n" => len
          | _ => find_ll (pos - 1, len + 1)
    in
      if p = 0 then raise exc (bad_prev ^
        "\nline: " ^ (Int.toString l) ^ ", col: " ^ (Int.toString c))
      else case String.sub (#buf buf, p - 1) of
          #"\n" => { pos = p - 1, line = l - 1, col = find_ll (p - 1, 1) }
        | _ => { pos = p - 1, line = l, col = c - 1 }
    end
  fun pos (buf: t): int = #pos (!(#point buf))
  fun line (buf: t): int = #line (!(#point buf))
  fun col (buf: t): int = #col (!(#point buf))
  fun eof (buf: t): bool =
    (String.size (#buf buf) <= 0) orelse (String.size (#buf buf) <= pos buf)
  fun peek (buf: t): char = String.sub (#buf buf, pos buf)
  fun try_peek (buf: t): char option =
    if eof buf then NONE else SOME (peek buf)
  fun advance (buf: t): t =
    case try_peek buf of
      NONE => buf
    | SOME #"\n" => (#point buf := Mark.new_line (point buf); buf)
    | SOME _ => (#point buf := Mark.advance (point buf); buf)
  fun substring (buf: t, i: int, j: int) = String.substring (#buf buf, i, j)

  fun start (buf: t, msg: string): token =
    let val tok = !(#next_tok buf)
    in (
      (#marks buf) := (msg, point buf, tok) :: !(#marks buf);
      (#next_tok buf) := tok + 1;
      tok
    ) end
  fun success (buf: t, tok: token): slice =
    let
      val marks = #marks buf
      val start = case !marks of
          [] => raise exc (succeed_no_start ^
            "\nline: " ^ (Int.toString (line buf)) ^
            ", col: " ^ (Int.toString (col buf)))
        | ((_,p,t)::ms) =>
          if t = tok
          then (marks := ms; p)
          else raise exc (bad_token ^
            "\nexpected: " ^ (Int.toString t) ^
            "\nreceived: " ^ (Int.toString tok))
    in
      (* TODO: check for off by one-ish *)
      { start = start, finish = (prev_point buf) }
    end

  fun expected_token (buf: t, tok: token): bool =
    case !(#marks buf) of
      [] => false
    | (_,_,t)::_ => tok = t

  fun failure (buf: t, tok: token, msg: string): string =
    let
      (* TODO: This is ass *)
      fun build_msg (txt, { pos, line, col }): string =
        msg ^ "\n" ^ (Int.toString line) ^ ":" ^ (Int.toString col) ^ " " ^ txt
    in case !(#marks buf) of
        [] => raise exc (fail_no_start ^
          "\nline: " ^ (Int.toString (line buf)) ^
          ", col: " ^ (Int.toString (col buf)))
      | (m,p,t)::ms =>
        if t = tok
        then (#marks buf := ms; build_msg (m, p))
    else raise exc (bad_token ^
      "\nexpected: " ^ (Int.toString t) ^
      "\nreceived: " ^ (Int.toString tok))
    end

  fun fromString (str: string): t =
    { buf = str, point = ref { pos = 0, line = 1, col = 1 }, marks = ref [],
      next_tok = ref 0 }
  fun fromStream (ss: TextIO.instream): t =
    let val str = TextIO.inputAll ss
    in fromString str
    end
end

structure Reader :> sig
  type t
  datatype item =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector

  val source: t -> Source.slice
  val item: t -> item
  val read: Source.t -> (t, string) result
  val splice: t -> t
  val pp: t -> string
end = struct
  (* TODO: figure out how to only have one definition *)
  datatype item =
    ATOM of string
  | LIST of t vector
  | FOREST of t vector
  withtype t = { source: Source.slice, item: item }

  fun source (t: t) = #source t
  fun item (t: t) = #item t

  (* TODO: some chars can be after the initial pos but not in *)
  fun isAtomChar (c: char): bool =
    let
      fun oneOf str =
        let fun helper i =
          if i >= String.size str then false
          else if String.sub (str, i) = c then true
          else helper (i + 1)
        in helper 0
        end
    in
      ((c >= #"A") andalso (c <= #"Z")) orelse
      ((c >= #"a") andalso (c <= #"z")) orelse
      ((c >= #"0") andalso (c <= #"9")) orelse
      oneOf "-=!@#$%^&*_+,./<>?;:~"
    end

  fun isWhitespace (c: char): bool =
    case c of
      #" " => true
    | #"\n" => true
    | #"\t" => true
    | _ => false

  (* TODO: should splicing an atom be allowed? return a result? *)
  fun splice { source, item = LIST ls } =
      { source = source, item = FOREST ls }
    | splice { source, item = FOREST ls } =
      { source = source, item = FOREST ls }
    | splice { source, item = ATOM s } =
      let val it = Vector.fromList [{ source = source, item = ATOM s }]
      in { source = source, item = FOREST it }
      end

  fun pp (e: t): string =
    case #item e of
      ATOM s => s
    | LIST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else " ") ^ (pp e))
      in "(" ^ ((fn (_, x) => x) (Vector.foldl f (true, "") l)) ^ ")"
      end
    | FOREST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else "\n") ^ (pp e))
      in (fn (_, x) => x) (Vector.foldl f (true, "") l)
      end

  local
    fun readAtom (buf: Source.t): t =
      let
        val start = Source.pos buf
        val tok = Source.start (buf, "reading an atom")
        fun helper n =
          case Source.try_peek buf of
            NONE => {
              source = Source.success (buf, tok),
              item = ATOM (Source.substring (buf, start, n))
            }
          | SOME c =>
            if isAtomChar c
            then (Source.advance buf; helper (n + 1))
            else {
              source = Source.success (buf, tok),
              item = ATOM (Source.substring (buf, start, n))
            }
      in helper 0
      end

    and readList (buf: Source.t): (t, string) result =
      let
        val tok = Source.start (buf, "reading a list")
        fun helper res =
          case Source.try_peek buf of
            NONE => Err (Source.failure (buf, tok, "couldn't find list end"))
          | SOME #")" =>
            (Source.advance buf; Ok {
              source = Source.success (buf, tok),
              item = LIST (Vector.fromList (List.rev res))
            })
          | _ => case readHelper buf of
              NONE => Err (Source.failure (buf, tok, "couldn't find list end"))
            | SOME r => case r of
                Err e => Err (Source.failure (buf, tok, e))
              | Ok v => helper (v :: res)
      in (Source.advance buf; helper [])
      end

    and readForest (res: t list) (buf: Source.t): (t, string) result =
      let
        (* TODO: better terminology *)
        val tok = Source.start (buf, "reading forest");
      in
        case readHelper buf of
          NONE => Ok {
            source = Source.success (buf, tok),
            item = FOREST (Vector.fromList (List.rev res))
          }
        | SOME r => case r of
          Err e => Err (Source.failure (buf, tok, e))
        | Ok v => readForest (v :: res) buf
      end

    and readHelper (buf: Source.t): (t, string) result option =
      if Source.eof buf then NONE
      else case Source.peek buf of
        #"(" => SOME (readList buf)
      | c =>
        if isWhitespace c then readHelper (Source.advance buf)
        else if isAtomChar c then SOME (Ok (readAtom buf))
        else SOME (Err "unexpected character")
  in
    fun read buf = case readForest [] buf of
        Ok x => Ok x
      | Err e => (fn { line, col, pos } =>
          Err ((Int.toString line) ^ ":" ^ (Int.toString col) ^ " " ^ e))
        (Source.point buf)
  end
end

structure Parser :> sig
  type t
  datatype item =
    PRIMOP of primop
  | ATOM of string
  | FUNCALL of t * (t vector)
  | FOREST of t vector

  and primop =
    CLAIM of string * t
  | ALIAS of string * t
  | LAMBDA
  | FUNCTION of t vector * t
  | BIND
  | SUM of t vector
  | PROD
  | MATCH
  | EQUAL
  | SCHEMA of { params: t vector, indices: t vector, prims: t vector }
  | TYPE of int

  val pp: t -> string
  val source: t -> Source.slice
  val item: t -> item
  val parse: Reader.t -> (t, string) result
end = struct
  datatype item =
    PRIMOP of primop
  | ATOM of string
  | FUNCALL of t * (t vector)
  | FOREST of t vector

  and primop =
    CLAIM of string * t
  | ALIAS of string * t
  | LAMBDA
  | FUNCTION of t vector * t
  | BIND
  | SUM of t vector
  | PROD
  | MATCH
  | EQUAL
  | SCHEMA of { params: t vector, indices: t vector, prims: t vector }
  | TYPE of int
  withtype t = { source: Source.slice, item: item }

  fun pp_forest (v: t vector): string =
    let fun f (0, e, _) = pp e
          | f (_, e, acc) = acc ^ " " ^ (pp e)
    in (Vector.foldli f "" v)
    end

  and pp_list (v: t vector): string = "(" ^ (pp_forest v) ^ ")"

  and pp (p: t): string =
    case #item p of
      PRIMOP p' => (
        case p' of
          CLAIM (s, t) => "(claim " ^ s ^ " " ^ (pp t) ^ ")"
        | ALIAS (s, t) => "(alias " ^ s ^ " " ^ (pp t) ^ ")"
        | TYPE l => "(Type " ^ (Int.toString l) ^ ")"
        | FUNCTION (args, res) =>
          "(-> " ^ (pp_forest args) ^ " " ^ (pp res) ^ ")"
        | SUM ss => "(sum " ^ (pp_forest ss) ^ ")"
        | SCHEMA { params, indices, prims } =>
          "(schema " ^ (pp_list params) ^ " " ^ (pp_list indices) ^ " " ^
            (pp_forest prims) ^ ")"
        | _ => raise unimplemented "Parser.pp primop"
      )
    | ATOM a => a
    | FUNCALL (fname, l) =>
      "(" ^ (pp fname) ^ (if Vector.length l = 0 then "" else pp_forest l) ^ ")"
    | FOREST l =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else "\n") ^ (pp e))
      in (fn (_, x) => x) (Vector.foldl f (true, "") l)
      end

  fun source (p: t): Source.slice = #source p
  fun item (p: t): item = #item p

  fun error (it: Reader.t, err: string): ('a, string) result =
    let
      val start = #start (Reader.source it)
      val finish = #finish (Reader.source it)
      val sl = Int.toString (#line start)
      val sc = Int.toString (#col start)
      val fl = Int.toString (#line finish)
      val fc = Int.toString (#col finish)
    in Err (sl ^ ":" ^ sc ^ "-" ^ fl ^ ":" ^ fc ^ " error: " ^ err)
    end

  fun add_source (r: Reader.t) (i: item): (t, 'a) result =
    Ok { source = Reader.source r, item = i }

  fun parse_vector (vs: Reader.t vector): (t vector, string) result =
    let
      fun f (0, _, acc) = acc
        | f (_, _, Err e) = Err e
        | f (_, v, Ok acc) = parse v >>= (fn v => Ok (v :: acc))
    in Vector.foldli f (Ok []) vs >>= (fn vs =>
      Ok (Vector.fromList vs))
    end

  and parseClaim (ls: Reader.t vector): (item, string) result =
    if Vector.length ls <> 3
    then error (Vector.sub (ls, 0), "CLAIM must have exactly 2 arguments")
    else let
        val tok = Vector.sub (ls, 0)
        val id = Vector.sub (ls, 1)
        val expr = Vector.sub (ls, 2)
      in case Reader.item id of
          Reader.ATOM a => parse expr >>= (fn x => Ok (PRIMOP (CLAIM (a, x))))
        | _ => error (id, "first argument of CLAIM must be an identifier")
      end

  and parseAlias (ls: Reader.t vector): (item, string) result =
    if Vector.length ls <> 3
    then error (Vector.sub (ls, 0), "ALIAS must have exactly 2 arguments")
    else let
        val tok = Vector.sub (ls, 0)
        val id = Vector.sub (ls, 1)
        val expr = Vector.sub (ls, 2)
      in case Reader.item id of
          Reader.ATOM a => parse expr >>= (fn x => Ok (PRIMOP (ALIAS (a, x))))
        | _ => error (id, "first argument of ALIAS must be an identifier")
      end

  and parseType (ls: Reader.t vector): (t, string) result =
    if Vector.length ls <> 2
    then error (Vector.sub (ls, 0), "Type must have exactly 1 argument")
    else let
        val lvl = Vector.sub (ls, 1)
        fun err () = error (lvl, "Type expects a non-negative int argument")
      in case Reader.item lvl of
          Reader.ATOM a => (
            case Int.fromString a of
              SOME x => if x < 0 then err () else Ok {
                source = Reader.source (Vector.sub (ls, 0)),
                item = PRIMOP (TYPE x) }
            | NONE => err ()
          )
        | _ => err ()
      end

  and parseSum (ls: Reader.t vector): (item, string) result =
    if Vector.length ls < 2
    then error (Vector.sub (ls, 0), "sum expects at least one argument")
    else parse_vector ls >>= (fn ls => Ok (PRIMOP (SUM ls)))

  and parseSchema (ls: Reader.t vector): (item, string) result =
    if Vector.length ls < 4
    then error (Vector.sub (ls, 0), "SCHEMA expects at least 3 arguments")
    else let
        val params = Vector.sub (ls, 1)
        val indices = Vector.sub (ls, 2)
        val prims = VectorSlice.vector (VectorSlice.slice (ls, 2, NONE))
      in
        (case parse (Reader.splice params) of
            Ok { source, item = FOREST ls } => Ok ls
          | Err e => Err e
          | _ => error (params,
              "internal error: parsing a forest should return a forest")
        ) >>= (fn pa =>
        (case parse (Reader.splice indices) of
            Ok { source, item = FOREST ls } => Ok ls
          | Err e => Err e
          | _ => error (indices,
              "internal error: parsing a forest should return a forest")
        ) >>= (fn i =>
        parse_vector prims >>= (fn pr =>
        Ok (PRIMOP (SCHEMA { params = pa, indices = i, prims = pr })))))
      end

  and parseFunc (ls: Reader.t vector): (item, string) result =
    if Vector.length ls < 3
    then error (Vector.sub (ls, 0), "-> expects at least two arguments")
    else let
        val numargs = Vector.length ls - 2
        val result = Vector.sub (ls, numargs)
        val args = VectorSlice.vector (
          VectorSlice.slice (ls, 0, SOME (numargs+1)))
      in parse result >>= (fn result =>
        parse_vector args >>= (fn args =>
        Ok (PRIMOP (FUNCTION (args, result)))))
      end

  and parse (r: Reader.t): (t, string) result =
    (* TODO: some work is needed here to ensure CLAIM, etc are only top-level *)
    case Reader.item r of
      Reader.FOREST ss =>
        let
          fun f (r, Err e) =
              (case parse r of Err e' => Err (e ^ "\n" ^ e') | _ => Err e)
            | f (r, Ok rs) =
              parse r >>= (fn x => Ok (Vector.concat [rs, Vector.fromList [x]]))
          val init = Ok (Vector.fromList [])
        in Vector.foldl f init ss >>=
          (fn x => Ok { source = Reader.source r, item = FOREST x })
        end
    | Reader.LIST ls =>
      if Vector.length ls = 0
      then error (r, "empty function call")
      else (
        let
          val fst = Vector.sub (ls, 0)
          fun f i = Vector.sub (ls, i+1)
          val rst = Vector.tabulate ((Vector.length ls)-1, f)
        in case Reader.item fst of
            Reader.FOREST _ =>
              error (fst, "internal error: found a forest inside a list")
          | Reader.LIST ls =>
              parse fst >>= (fn fst =>
              parse_vector rst >>= (fn rst =>
              Ok { source = Reader.source r, item = FUNCALL (fst, rst) }))
          | Reader.ATOM "claim" => parseClaim ls >>= add_source r
          | Reader.ATOM "alias" => parseAlias ls >>= add_source r
          | Reader.ATOM "Type" => parseType ls
          | Reader.ATOM "sum" => parseSum ls >>= add_source r
          | Reader.ATOM "schema" => parseSchema ls >>= add_source r
          | Reader.ATOM "->" => parseFunc ls >>= add_source r
          | Reader.ATOM a => parse_vector rst >>= (fn rst =>
              let val fst = { source = Reader.source fst, item = ATOM a }
              in Ok { source = Reader.source r, item = FUNCALL (fst, rst) }
              end)
        end
      )
    | Reader.ATOM "claim" => error (r, "CLAIM must be used as a function")
    | Reader.ATOM "alias" => error (r, "ALIAS must be used as a function")
    | Reader.ATOM "sum" => error (r, "SUM must be used as a function")
    | Reader.ATOM "prim" => error (r, "PRIM must be used as a function")
    | Reader.ATOM "schema" => error (r, "SCHEMA must be used as a function")
    | Reader.ATOM "->" => error (r, "-> must be used as a function")
    | Reader.ATOM a => Ok { source = Reader.source r, item = ATOM a }
end

structure Typer :> sig
  type t
  val print_tables: t -> string
  val check: Parser.t -> (t, string) result
end = struct
  structure TypeTable = HashMap(
    type value = { orig: Parser.t, norm: Type.t }
    structure H = StringHasher)
  structure ValueTable = HashMap(
    type value = { orig: Parser.t, def: Value.t }
    structure H = StringHasher)
  structure PrimitiveTable = HashMap(
    type value = { orig: Parser.t, prim: Type.t }
    structure H = IntHasher)

  type tables = {
    types: TypeTable.t,
    values: ValueTable.t,
    next_prim: int,
    prims: PrimitiveTable.t
  }
  type t = {
    types: TypeTable.t,
    values: ValueTable.t,
    code: Parser.t
  }

  fun print_tables ({ types, values, code }: t): string =
    TypeTable.fold
      (fn ((_,k,v), str) => str ^ "\n" ^ k ^ ": " ^ (Parser.pp (#orig v)))
      "" types

  fun err_pos (p: Parser.t): string =
    let
      val start = #start (Parser.source p)
      val finish = #finish (Parser.source p)
      val sl = Int.toString (#line start)
      val sc = Int.toString (#col start)
      val fl = Int.toString (#line finish)
      val fc = Int.toString (#col finish)
    in sl ^ ":" ^ sc ^ "-" ^ fl ^ ":" ^ fc
    end

  fun error (p: Parser.t, err: string): ('a, string) result =
     Err ((err_pos p) ^ " error: " ^ err)

  (* TODO: should this be combined with the helper function? *)
  fun normalise (state: tables, p: Parser.t): (Type.t, string) result =
    case Parser.item p of
      Parser.FOREST _ =>
        error (p, "internal error: unexpected FOREST during type normalisation")
    | Parser.PRIMOP pop => (
        case pop of
          Parser.CLAIM _ => error (p,
            "internal error: unexpected CLAIM during type normalisation")
        | Parser.ALIAS _ => error (p,
            "internal error: unexpected ALIAS during type normalisation")
        | Parser.TYPE x => Ok (Type.LEVEL x)
        | Parser.SCHEMA _ => error (p,
            "internal error: unexpected SCHEMA during type normalisation")
        | Parser.SUM ss => normalise (state, (Vector.sub (ss, 0))) >>=
          (fn fst => let
            fun f (0, _, Ok acc) = Ok acc
              | f (_, _, Err e) = Err e
              | f (_, s, Ok acc) = normalise (state, s) >>= (fn s' =>
                if (Type.result fst) = (Type.result s')
                then Ok (s' :: acc)
                else error (s, "expecting a type compatible with `"
                  ^ (Type.pp fst) ^ "`, but found type `" ^ (Type.pp s') ^ "`"))
          in Vector.foldri f (Ok []) ss >>= (fn ss =>
            Ok (Type.SUM (Vector.fromList (fst :: ss))))
          end)
        | Parser.FUNCTION (args, result) =>
          let
            val result = normalise (state, result)
            fun f (_, Err e) = Err e
              | f (l, Ok ls) = normalise (state, l) >>= (fn l => Ok (l :: ls))
            val argsls = Vector.foldr f (Ok []) args
            fun mkvec ls = Vector.fromList ls
          in result >>= (fn result =>
            argsls >>= (fn args =>
            Ok (Type.FUN (mkvec args, result))))
          end
        | _ => raise unimplemented "norm primop"
      )
    | Parser.ATOM a => (
        case TypeTable.try_get (#types state, a) of
          SOME { orig, norm } => Ok norm
        | NONE => error (p, "encountered identifier without declared type")
      )
    | Parser.FUNCALL (fst, rst) => normalise (state, fst) >>= (
        fn (Type.FUN (args, ret)) =>
            if Vector.length rst <> Vector.length args
            then error (p, "function expected " ^
              (Int.toString (Vector.length args)) ^ " arguments")
            else raise unimplemented "normalise function"
        | ty => error (fst,
            "expected FUNCTION type but found\n" ^ (Type.pp ty))
      )

  (*
   * TODO: Is this right for identifiers? It should say Nat.zero is of type
   * Nat not of type (Type 0)
   *)
  fun reduce (state: tables, p: Parser.t): (tables * Value.t, string) result =
    case Parser.item p of
      Parser.FOREST _ =>
        error (p, "internal error: unexpected FOREST during reduction")
    | Parser.PRIMOP pop => (
        case pop of
          Parser.CLAIM _ =>
            error (p, "internal error: unexpected CLAIM during reduction")
        | Parser.ALIAS _ =>
            error (p, "internal error: unexpected ALIAS during reduction")
        | Parser.TYPE x => Ok (state, Value.TYPE (Type.LEVEL x))
        | Parser.SCHEMA { params, indices, prims } =>
          raise unimplemented "Typer.reduce SCHEMA"
(*
        | Parser.PRIM ts =>
          let
            val num = #next_prim state
            fun f (_, Err e) = Err e
              | f (t, Ok ts) = normalise (state, t) >>= (fn t => Ok (t::ts))
            fun prims' tys = {
              next_prim = num + 1,
              values = #values state,
              types = #types state,
              prims = PrimitiveTable.insert (#prims state, num, {
                orig = p, prim = Type.PRIM tys }) }
          in Vector.foldl f (Ok []) ts >>= (fn tys =>
            Ok (prims' (Vector.fromList (List.rev tys)), Value.PRIM num))
          end
*)
        | Parser.SUM ss =>
          if Vector.length ss = 0
          then error (p, "sum type cannot be empty; expected value")
          else normalise (state, Vector.sub (ss, 0)) >>= (fn fst =>
            let
            fun f (0, _, Ok acc) = Ok acc
              | f (_, _, Err e) = Err e
              | f (_, s, Ok acc) = normalise (state, s) >>= (fn s' =>
                if (Type.result fst) = (Type.result s')
                then Ok (s' :: acc)
                else error (s, "expecting a type compatible with `"
                  ^ (Type.pp fst) ^ "`, but found type `" ^ (Type.pp s') ^ "`"))
          in Vector.foldri f (Ok []) ss >>= (fn ss =>
            Ok (state, Value.TYPE (Type.SUM (
              Vector.fromList (fst :: ss)))))
          end)
        | _ => raise unimplemented "Typer.reduce primop"
      )
    | _ => raise unimplemented "Typer.reduce top-level"

  fun get_type (state: tables, p: Parser.t): (Type.t, string) result =
    case Parser.item p of
      Parser.FOREST _ =>
        error (p, "internal error: unexpected FOREST during typing")
    | Parser.PRIMOP pop => (
        case pop of
          Parser.CLAIM _ => 
            error (p, "internal error: unexpected CLAIM during typing")
        | Parser.ALIAS _ =>
            error (p, "internal error: unexpected ALIAS during typing")
        | Parser.TYPE x => Ok (Type.LEVEL (x + 1))
        | Parser.SCHEMA { params, indices, prims } =>
          let
            fun tt (_, Err e) = Err e
              | tt (v, Ok vs) = normalise (state, v) >>= (fn v => Ok (v :: vs))
            fun to_types vs = Vector.foldr tt (Ok []) vs >>= (fn ls =>
              Ok (Vector.fromList ls))
          in
            to_types params >>= (fn params =>
            to_types indices >>= (fn indices =>
            let
              val merged = Vector.concat [params, indices]
              fun f (ty, lvl) = max (Type.level ty, lvl)
            in Ok (
              if Vector.length merged = 0
              then Type.LEVEL 0
              else Type.FUN (merged, Type.LEVEL (Vector.foldl f 0 merged)))
            end))
          end
        | Parser.SUM ss =>
          let
            fun f (_, Err e) = Err e
              | f (s, Ok lvl) = get_type (state, s) >>= (
                fn Type.LEVEL l => Ok (if l > lvl then l else lvl)
                 | _ => Ok 0)
          in Vector.foldl f (Ok 0) ss >>= (fn lvl => Ok (Type.LEVEL lvl))
          end
        | _ => raise unimplemented "Typer.get_type primop"
      )
    | Parser.FUNCALL (fname, ls) => raise unimplemented "Typer.get_type FUNCALL"
    | Parser.ATOM a => (
      case TypeTable.try_get (#types state, a) of
          NONE => error (p, "usage of identifier with unknown type: " ^ a)
        | SOME { norm, orig } => Ok norm
      )

  fun check (p: Parser.t): (t, string) result =
    let
      fun wrapty
        ({ types, values, prims, next_prim }: tables, id: string,
          orig: Parser.t)
        (ty: Type.t)
      =
        case TypeTable.insertOrGet (types, id, { orig = orig, norm = ty }) of
          TypeTable.INSERT t => Ok {
            values = values, types = t, prims = prims, next_prim = next_prim }
        | TypeTable.GET p => raise unimplemented "type check wrap type get"
      fun wrapva
        (id: string, orig: Parser.t)
        ({ types, values, prims, next_prim }: tables, va: Value.t)
      =
        case ValueTable.insertOrGet (values, id, { orig = orig, def = va }) of
          ValueTable.INSERT v => Ok {
            values = v, types = types, prims = prims, next_prim = next_prim }
        | ValueTable.GET p => raise unimplemented "type check wrap value get"

      fun helper (it: Parser.t, state: tables): (tables, string) result =
        case Parser.item it of
          Parser.FOREST ls =>
            let fun f (x, acc) = acc >>= (fn a => helper (x, a))
            in Vector.foldl f (Ok state) ls
            end
        | Parser.PRIMOP pop => (
            case pop of
              Parser.CLAIM (id, x) =>
                normalise (state, x) >>= wrapty (state, id, x)
            | Parser.ALIAS (id, x) => (
                (*
                 * TODO: We need to walk this tree and for every PRIM, add an
                 * entry in to the types table.
                 *)
                case TypeTable.try_get (#types state, id) of
                  NONE => raise unimplemented "check alias"
                | SOME tyl => get_type (state, x) >>= (fn tyr =>
                  if Type.eq (#norm tyl, tyr)
                  then reduce (state, x) >>= wrapva (id, x)
                  else error (it, "type mismatch: `" ^ id ^ "`"
                    ^ " previously declared as `"
                    ^ (Parser.pp (#orig tyl)) ^ "` at "
                    ^ (err_pos (#orig tyl)) ^ ", but `" ^ (Parser.pp x)
                    ^ "` is of type `" ^ (Type.pp tyr) ^ "`")
                  )
              )
            | _ => raise unimplemented "check primop"
          )
        | _ => Ok state
      val init = {
        values = ValueTable.empty (),
        types = TypeTable.empty (),
        prims = PrimitiveTable.empty (),
        next_prim = 0 }
    in case helper (p, init) of
        Ok { types, values, prims, next_prim } => Ok {
          types = types, values = values, code = p }
      | Err y => Err y
    end
end

fun main () =
  let
    val source = Source.fromStream TextIO.stdIn
    val checked = (Reader.read source) >>= Parser.parse >>= Typer.check
    val repr = case checked of Ok t => Typer.print_tables t | Err e => e
  in TextIO.output (TextIO.stdOut, repr ^ "\n")
  end

val _ = main ()
