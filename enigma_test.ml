open OUnit2
open Enigma

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input)

let rotor_i = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_iii = "BDFHJLCPRTXVZNYEIWGAKMUSQO"

let map_r_to_l_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_r_to_l wiring top_letter input_pos)

let map_l_to_r_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_l_to_r wiring top_letter input_pos)

let map_refl_test name wiring input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_refl wiring input_pos)

let map_plug_test name plugs input expected =
  name >:: fun _ ->
    assert_equal expected (map_plug plugs input)

let cipher_char_test name config input expected =
  name >:: fun _ ->
    assert_equal expected (cipher_char config input)

let step_test name config expected_top_letters =
  name >:: fun _ ->
    let stepped = step config in
    let letters = List.map (fun r -> r.top_letter) stepped.rotors in
    assert_equal expected_top_letters letters

let cipher_test name config input expected =
  name >:: fun _ ->
    assert_equal expected (cipher config input)

let identity_rotor = {
  wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  turnover = 'A';
}

let rotor_i_cfg = { rotor = { wiring = rotor_i; turnover = 'Q' }; top_letter = 'A' }
let rotor_ii_cfg = { rotor = { wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE"; turnover = 'E' }; top_letter = 'A' }
let rotor_iii_cfg = { rotor = { wiring = rotor_iii; turnover = 'V' }; top_letter = 'A' }

let config_example = {
  refl = "YRUHQSLDPXNGOKMIEBFZCWVJATH";
  rotors = [ rotor_i_cfg; rotor_ii_cfg; rotor_iii_cfg ];
  plugboard = [];
}

let suite =
  "Enigma test suite" >::: [
    index_test "index of A is 0" 'A' 0;
    index_test "index of Z is 25" 'Z' 25;

    map_r_to_l_test "identity rotor maps input to same position" "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 0;
    map_r_to_l_test "rotor I with top A maps position 0 to 4" rotor_i 'A' 0 4;
    map_r_to_l_test "rotor I with top B maps position 0 to 9" rotor_i 'B' 0 9;
    map_r_to_l_test "rotor III at O with top O yields 17" rotor_iii 'O' 14 17;

    map_l_to_r_test "identity rotor reverse maps position 0 to 0" "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 0;
    map_l_to_r_test "rotor I left to right at top A maps 0 to 20" rotor_i 'A' 0 20;
    map_l_to_r_test "rotor I maps input 10 from F to 14" rotor_i 'F' 10 14;

    map_refl_test "identity reflector keeps letters fixed" "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 0 0;
    map_refl_test "identity reflector keeps Z fixed" "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 25 25;
    map_refl_test "reflector B maps input 0 to the index of Y" "YRUHQSLDPXNGOKMIEBFZCWVJATH" 0 24;

    map_plug_test "empty plugboard leaves M unchanged" [] 'M' 'M';
    map_plug_test "plugboard swaps A and Z" [('A', 'Z')] 'A' 'Z';
    map_plug_test "plugboard swaps X and Y in both directions" [('A', 'Z'); ('X', 'Y')] 'X' 'Y';
    map_plug_test "plugboard leaves unconnected letter unchanged" [('A', 'Z'); ('X', 'Y')] 'C' 'C';

    cipher_char_test "identity machine keeps A unchanged" {
      refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
      rotors = [ { rotor = identity_rotor; top_letter = 'A' } ];
      plugboard = [];
    } 'A' 'A';
    cipher_char_test "identity machine keeps B unchanged" {
      refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
      rotors = [ { rotor = identity_rotor; top_letter = 'A' } ];
      plugboard = [];
    } 'B' 'B';
    cipher_char_test "historical example G maps to P" {
      refl = "YRUHQSLDPXNGOKMIEBFZCWVJATH";
      rotors = [
        { rotor = { wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; turnover = 'Q' }; top_letter = 'A' };
        { rotor = { wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE"; turnover = 'E' }; top_letter = 'A' };
        { rotor = { wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; turnover = 'V' }; top_letter = 'A' };
      ];
      plugboard = [];
    } 'G' 'P';

    step_test "rightmost rotor advances and propagates turnover" {
      refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
      rotors = [
        { rotor = { wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; turnover = 'A' }; top_letter = 'A' };
        { rotor = { wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; turnover = 'A' }; top_letter = 'A' };
      ];
      plugboard = [];
    } ['B'; 'B'];

    step_test "turnover on middle rotor propagates left" {
      refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
      rotors = [
        { rotor = { wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; turnover = 'A' }; top_letter = 'A' };
        { rotor = { wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; turnover = 'A' }; top_letter = 'A' };
        { rotor = { wiring = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; turnover = 'A' }; top_letter = 'A' };
      ];
      plugboard = [];
    } ['B'; 'B'; 'B'];

    cipher_test "cipher on empty string is empty" config_example "" "";
    cipher_test "cipher keeps identity config stable" {
      refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
      rotors = [ { rotor = identity_rotor; top_letter = 'A' } ];
      plugboard = [];
    } "ABC" "ABC";
  ]

let () = run_test_tt_main suite
