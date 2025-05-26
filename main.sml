fun prn (str: string): unit = TextIO.output (TextIO.stdOut, str ^ "\n")
exception unimplemented of string

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
    (* TODO: uint? *)
  | LEVEL of int
  | PRIM

  val pp: t -> string
  val result: t -> t
end = struct
  datatype t =
    FUN of (t vector) * t
  | SUM of t vector
  | PROD of t vector
  | LEVEL of int
  | PRIM

  fun pp (t: t): string =
    case t of
      FUN (args, ret) => raise unimplemented "Type.pp fun"
    | SUM ss =>
      let fun f (s, acc) = acc ^ " " ^ (pp s)
      in "(sum" ^ (Vector.foldl f "" ss) ^ ")"
      end
    | PROD ps => raise unimplemented "Type.pp prod"
    | LEVEL l => "(Type " ^ (Int.toString l) ^ ")"
    | PRIM => "(prim)"

  fun result (FUN (_, r)) = r
    | result r = r
end

structure Value :> sig
  datatype t =
    LAM of unit
  | PRIM of int

  val pp: t -> string
  val typeof: t -> Type.t
end = struct
  datatype t =
    LAM of unit
  | PRIM of int

  fun pp _ = raise unimplemented "Value.pp"
  fun typeof _ = raise unimplemented "Value.typeof"
end

signature Hashable = sig
  eqtype t
  val hash: t -> word
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

  fun get_idx (buf: t, k: key): int =
    Word.toInt (Word.mod (H.hash k, Word.fromInt (!(#cap buf))))

  fun empty () = { buf = Array.array (7, []), len = ref 0, cap = ref 7 }
  fun fold (f: (word * key * value) * 'a -> 'a) (acc: 'a) (tbl: t): 'a =
    Array.foldl (fn (ls, acc) => List.foldl f acc ls) acc (#buf tbl)

  fun grow ({ buf, len = ref len, cap = ref cap }: t): t =
    raise unimplemented "bleh"

  fun tryGet
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
    case tryGet (tbl, k) of
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
      (* TODO: This *)
      fun build_msg (res, ms): string = msg
    in case !(#marks buf) of
        [] => raise exc (fail_no_start ^
          "\nline: " ^ (Int.toString (line buf)) ^
          ", col: " ^ (Int.toString (col buf)))
      | (m,p,t)::ms =>
        if t = tok
        then (#marks buf := ms; build_msg ("", !(#marks buf)))
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
      oneOf "!@#$%^&*_+,./<>?;:~"
    end

  fun isWhitespace (c: char): bool =
    case c of
      #" " => true
    | #"\n" => true
    | #"\t" => true
    | _ => false

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
    val read = readForest []
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
  | FUNCTION
  | BIND
  | SUM of t vector
  | PROD
  | MATCH
  | EQUAL
  | PRIM of string
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
  | FUNCTION
  | BIND
  | SUM of t vector
  | PROD
  | MATCH
  | EQUAL
  | PRIM of string
  | TYPE of int
  withtype t = { source: Source.slice, item: item }

  fun pp (p: t): string =
    case #item p of
      PRIMOP p' => (
        case p' of
          CLAIM (s, t) => "(claim " ^ s ^ " " ^ (pp t) ^ ")"
        | ALIAS (s, t) => "(alias " ^ s ^ " " ^ (pp t) ^ ")"
        | TYPE l => "(Type " ^ (Int.toString l) ^ ")"
        | SUM ss =>
          let fun f (e, acc) = acc ^ " " ^ (pp e)
          in "(sum" ^ (Vector.foldl f "" ss) ^ ")"
          end
        | PRIM id => "(prim " ^ id ^ ")"
        | _ => raise unimplemented "Parser.pp primop"
      )
    | ATOM a => a
    | FUNCALL (fname, l) =>
      let fun f (e, (fst, a)) = (false, a ^ (if fst then "" else " ") ^ (pp e))
      in "(" ^ (pp fname) ^ " " ^
        ((fn (_, x) => x) (Vector.foldl f (true, "") l)) ^ ")"
      end
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

  fun parseClaim (ls: Reader.t vector): (item, string) result =
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
    else let
        fun f (0, _, acc) = acc
          | f (_, _, Err e) = Err e
          | f (_, v, Ok acc) = parse v >>= (fn v => Ok (v :: acc))
      in Vector.foldli f (Ok []) ls >>= (fn vs =>
        Ok (PRIMOP (SUM (Vector.fromList vs))))
      end

  and parsePrim (ls: Reader.t vector): (item, string) result =
    if Vector.length ls <> 2
    then error (Vector.sub (ls, 0), "PRIM must have exactly 1 argument")
    else let val name = Vector.sub (ls, 1)
      in case Reader.item name of
          Reader.ATOM a => Ok (PRIMOP (PRIM a))
        | _ => error (name, "PRIM argument must be an identifier")
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
      then error (r, "empty function call. Did you mean the empty list, Nil?")
      else (
        let
          val fst = Vector.sub (ls, 0)
          fun p ls =
            let
              fun f (_, _, Err e) = Err e
                | f (0, _, a) = a
                | f (_, e, Ok vs) = parse e >>=
                  (fn x => Ok (Vector.concat [vs, Vector.fromList [x]]))
              val init = Ok (Vector.fromList [])
            in Vector.foldli f init ls
            end
        in case Reader.item fst of
            Reader.FOREST _ =>
              error (fst, "internal error: found a forest inside a list")
          | Reader.LIST ls => parse fst >>= (fn fst => p ls >>= (fn rst =>
              Ok { source = Reader.source r, item = FUNCALL (fst, rst) }))
          | Reader.ATOM "claim" => parseClaim ls >>= add_source r
          | Reader.ATOM "alias" => parseAlias ls >>= add_source r
          | Reader.ATOM "Type" => parseType ls
          | Reader.ATOM "sum" => parseSum ls >>= add_source r
          | Reader.ATOM "prim" => parsePrim ls >>= add_source r
          | Reader.ATOM a => p ls >>= (fn rst =>
              let val fst = { source = Reader.source fst, item = ATOM a }
              in Ok { source = Reader.source r, item = FUNCALL (fst, rst) }
              end)
        end
      )
    | Reader.ATOM "claim" => error (r, "CLAIM must be used as a function")
    | Reader.ATOM "alias" => error (r, "ALIAS must be used as a function")
    | Reader.ATOM "sum" => error (r, "SUM must be used as a function")
    | Reader.ATOM "prim" => error (r, "PRIM must be used as a function")
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

  type tables = { types: TypeTable.t, values: ValueTable.t }
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
        | Parser.SUM ss => normalise (state, (Vector.sub (ss, 0))) >>=
          (fn fst => let
            fun f (0, _, Ok acc) = Ok acc
              | f (_, _, Err e) = Err e
              | f (_, s, Ok acc) = normalise (state, s) >>= (fn s' =>
                if (Type.result fst) = (Type.result s')
                then Ok (s' :: acc)
                else error (s, "expecting a type compatible with `"
                  ^ (Type.pp fst) ^ "`, but found type `" ^ (Type.pp s') ^ "`"))
          in Vector.foldli f (Ok []) ss >>= (fn ss =>
            Ok (Type.SUM (Vector.fromList (fst :: (List.rev ss)))))
          end)
        | _ => raise unimplemented "norm primop"
      )
    | Parser.ATOM a => (
        case ValueTable.tryGet (#values state, a) of
          SOME { orig, def } => Ok (Value.typeof def)
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
        | Parser.PRIM _ => Ok (Type.LEVEL 0)
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
    | _ => raise unimplemented "Typer.get_type top-level"

  fun check (p: Parser.t): (t, string) result =
    let
      fun wrapty
        ({ types, values }: tables, id: string, orig: Parser.t) (ty: Type.t)
      =
        case TypeTable.insertOrGet (types, id, { orig = orig, norm = ty }) of
          TypeTable.INSERT t => Ok { values = values, types = t }
        | TypeTable.GET p => raise unimplemented "type check wrap type get"
      fun wrapva
        ({ types, values }: tables, id: string, orig: Parser.t) (va: Value.t)
      =
        case ValueTable.insertOrGet (values, id, { orig = orig, def = va }) of
          ValueTable.INSERT v => Ok { values = v, types = types }
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
                case TypeTable.tryGet (#types state, id) of
                  NONE => raise unimplemented "check alias"
                | SOME tyl => get_type (state, x) >>= (fn tyr =>
                  let
                    val a = ""
                  in
                    error (it, "type mismatch: `" ^ id ^ "`"
                      ^ " previously declared as `"
                      ^ (Parser.pp (#orig tyl)) ^ "` at "
                      ^ (err_pos (#orig tyl)) ^ ", but `" ^ (Parser.pp x)
                      ^ "` is of type `" ^ (Type.pp tyr) ^ "`")
                  end)
              )
            | _ => raise unimplemented "check primop"
          )
        | _ => Ok state
      val init = { values = ValueTable.empty (), types = TypeTable.empty () }
    in case helper (p, init) of
        Ok { types, values } => Ok { types = types, values = values, code = p }
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