(** A tiny JSON writer. The intermediate representation is ours end to end, so
    a dependency on a JSON library would buy nothing but a second escaping
    rule to keep in step. *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | Str of string
  | List of t list
  | Obj of (string * t) list

let add_utf8 buf code =
  if code < 0x80 then Buffer.add_char buf (Char.chr code)
  else if code < 0x800 then begin
    Buffer.add_char buf (Char.chr (0xC0 lor (code lsr 6)));
    Buffer.add_char buf (Char.chr (0x80 lor (code land 0x3F)))
  end else begin
    Buffer.add_char buf (Char.chr (0xE0 lor (code lsr 12)));
    Buffer.add_char buf (Char.chr (0x80 lor ((code lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (code land 0x3F)))
  end

(* Encode one UTF-8 scalar starting at [i]; return the number of bytes read. *)
let decode_utf8 s i =
  let n = String.length s in
  let b0 = Char.code s.[i] in
  if b0 < 0x80 then (b0, 1)
  else if b0 land 0xE0 = 0xC0 && i + 1 < n then
    (((b0 land 0x1F) lsl 6) lor (Char.code s.[i + 1] land 0x3F), 2)
  else if b0 land 0xF0 = 0xE0 && i + 2 < n then
    ( ((b0 land 0x0F) lsl 12)
      lor ((Char.code s.[i + 1] land 0x3F) lsl 6)
      lor (Char.code s.[i + 2] land 0x3F),
      3 )
  else if b0 land 0xF8 = 0xF0 && i + 3 < n then
    ( ((b0 land 0x07) lsl 18)
      lor ((Char.code s.[i + 1] land 0x3F) lsl 12)
      lor ((Char.code s.[i + 2] land 0x3F) lsl 6)
      lor (Char.code s.[i + 3] land 0x3F),
      4 )
  else
    (* Malformed input: keep the byte, the output stays valid ASCII. *)
    (b0, 1)

let escape buf s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    (match c with
    | '"' -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | '\b' -> Buffer.add_string buf "\\b"
    | '\012' -> Buffer.add_string buf "\\f"
    | _ ->
        let code = Char.code c in
        if code < 0x20 then Buffer.add_string buf (Printf.sprintf "\\u%04x" code)
        else if code < 0x80 then Buffer.add_char buf c
        else begin
          let scalar, len = decode_utf8 s !i in
          add_utf8 buf scalar;
          i := !i + len - 1
        end);
    incr i
  done

let rec write_r buf ~indent t =
  let pad n = String.make (2 * n) ' ' in
  match t with
  | Null -> Buffer.add_string buf "null"
  | Bool b -> Buffer.add_string buf (if b then "true" else "false")
  | Int i -> Buffer.add_string buf (string_of_int i)
  | Str s ->
      Buffer.add_char buf '"';
      escape buf s;
      Buffer.add_char buf '"'
  | List [] -> Buffer.add_string buf "[]"
  | List xs ->
      Buffer.add_string buf "[\n";
      List.iteri
        (fun i x ->
          Buffer.add_string buf (pad (indent + 1));
          write_r buf ~indent:(indent + 1) x;
          if i < List.length xs - 1 then Buffer.add_char buf ',';
          Buffer.add_char buf '\n')
        xs;
      Buffer.add_string buf (pad indent);
      Buffer.add_char buf ']'
  | Obj [] -> Buffer.add_string buf "{}"
  | Obj fields ->
      Buffer.add_string buf "{\n";
      List.iteri
        (fun i (k, v) ->
          Buffer.add_string buf (pad (indent + 1));
          Buffer.add_char buf '"';
          escape buf k;
          Buffer.add_string buf "\": ";
          write_r buf ~indent:(indent + 1) v;
          if i < List.length fields - 1 then Buffer.add_char buf ',';
          Buffer.add_char buf '\n')
        fields;
      Buffer.add_string buf (pad indent);
      Buffer.add_char buf '}'

let to_string t =
  let buf = Buffer.create 4096 in
  write_r buf ~indent:0 t;
  Buffer.add_char buf '\n';
  Buffer.contents buf
