structure Source = struct
    type t = {
        buf : string,
        pos : int ref
    }

    fun eof (buf: t): bool = String.size (#buf buf) <= 0
    fun peek (buf: t): char = String.sub (#buf buf, 0)
    fun advance (buf: t): t = ((#pos buf) := !(#pos buf) + 1; buf)
    fun fromString (str: string): t = { buf = str, pos = ref 0 }
    fun fromStream (ss: TextIO.instream): t =
        let val str = TextIO.inputAll ss
        in fromString str
        end
end

datatype expr =
    ATOM of string
    LIST of expr vector

fun isAtomChar (c: char): bool = 
    if (c <= #"A") then true else false

fun parseAtom (buf: Source.t): expr = ATOM "atom"
fun parseList (buf: Source.t): expr option = SOME (ATOM "list")

fun parseExpr (buf: Source.t): expr option = 
    if Source.eof buf then NONE else
    case Source.peek buf of 
        #"(" => parseList (Source.advance buf)
        _ => SOME (parseAtom buf)

fun ppExpr (e: expr): string = 
    case e of
        ATOM s => s
        LIST l => 
        let fun f (e, a) = a ^ " " ^ (ppExpr e)
        in "(" ^ (Vector.foldl f "" l) ^ ")"
        end

fun main () = 
    let 
        val source = Source.fromStream TextIO.stdIn
        val prog = parseExpr source
        val repr = case prog of SOME p => ppExpr p | NONE => "ERROR YOU RETARD!!"
    in TextIO.output (TextIO.stdOut, repr ^ "\n")
    end

val _ = main ()