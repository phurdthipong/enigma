type rotor = {
  wiring : string;
  turnover : char;
}

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char * char) list;
}

let alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

let normalize_pos pos =
  let value = pos mod 26 in
  if value < 0 then value + 26 else value

let index c =
  Char.code c - Char.code 'A'

let next_letter c =
  let next_index = normalize_pos (index c + 1) in
  alphabet.[next_index]

let index_of_char s ch =
  let rec loop i =
    if i = String.length s then
      failwith "character not found"
    else if s.[i] = ch then
      i
    else
      loop (i + 1)
  in
  loop 0

let map_r_to_l wiring top_letter input_pos =
  let offset = index top_letter in
  let internal_in = normalize_pos (input_pos + offset) in
  let mapped = index wiring.[internal_in] in
  normalize_pos (mapped - offset)

let map_l_to_r wiring top_letter input_pos =
  let offset = index top_letter in
  let internal_in = normalize_pos (input_pos + offset) in
  let target = alphabet.[internal_in] in
  let inverse = index_of_char wiring target in
  normalize_pos (inverse - offset)

let map_refl wiring input_pos =
  let pos = normalize_pos input_pos in
  index wiring.[pos]

let rec map_plug plugs c =
  match plugs with
  | [] -> c
  | (a, b) :: rest ->
      if c = a then b
      else if c = b then a
      else map_plug rest c

let rec pass_r_to_l rotors pos =
  match rotors with
  | [] -> pos
  | rotor :: rest ->
      let next_pos = map_r_to_l rotor.rotor.wiring rotor.top_letter pos in
      pass_r_to_l rest next_pos

let rec pass_l_to_r rotors pos =
  match rotors with
  | [] -> pos
  | rotor :: rest ->
      let next_pos = map_l_to_r rotor.rotor.wiring rotor.top_letter pos in
      pass_l_to_r rest next_pos

let cipher_char config c =
  let letter = map_plug config.plugboard c in
  let pos = index letter in
  let after_rotors = pass_r_to_l (List.rev config.rotors) pos in
  let reflected = map_refl config.refl after_rotors in
  let output_pos = pass_l_to_r config.rotors reflected in
  let output_letter = Char.chr (Char.code 'A' + output_pos) in
  map_plug config.plugboard output_letter

let step config =
  let rec advance carry = function
    | [] -> []
    | rotor :: rest ->
        let should_step = carry || rest = [] in
        let next_top = if should_step then next_letter rotor.top_letter else rotor.top_letter in
        let carry_next = should_step && rotor.top_letter = rotor.rotor.turnover in
        { rotor = rotor.rotor; top_letter = next_top } :: advance carry_next rest
  in
  let rotated = advance true (List.rev config.rotors) in
  { config with rotors = List.rev rotated }

let rec cipher config s =
  if String.length s = 0 then
    ""
  else
    let first = s.[0] in
    let rest = String.sub s 1 (String.length s - 1) in
    let next_config = step config in
    let encoded = cipher_char next_config first in
    String.make 1 encoded ^ cipher next_config rest

let hours_worked = 12
