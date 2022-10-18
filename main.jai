main :: () {
  solver: Solver;
  open_cnf_file(*solver, "cnfs/uf20-01.cnf");
  for c: solver.clauses {
    print_clause(c.lit);
  }
}

open_cnf_file :: (solver: *Solver, filename: string) -> success: bool = false {
  textfile, success := read_entire_file(filename);
  if !success {
    return;
  }

  numvars := -1;
  numclauses := -1;

  // parse premable.
  while textfile {
    found, left, right := split_from_left(textfile, #char "\n");
    textfile = right;
    header := parse_token(*left);
    if header ==  {
    case "c"; 
      // do nothing
    case "p";
      problem := parse_token(*left);
      if equal(problem, "cnf") {
        numvars, success = parse_int(*left);
        if !success || numvars < 1 {
          print("Error. Invalid number of variables\n");
          return;
        }
        numclauses, success = parse_int(*left);
        if !success || numclauses < 1 {
          print("Error. Invalid number of clauses\n");
          return;
        }
      }
      textfile = right;
      break;
    case;
      print("Error. Token\n");
      return;
    }
  }

  if numvars < 1 || numclauses < 1 {
    print("Invalid number of variables/clauses\n");
    return;
  }

  clauses: [..] Clause;
  array_reserve(*clauses, (3 * numclauses) / 2);
  array: [..] Lit;
  array.allocator = temp;
  array_reserve(*array, 20);
  val: int;
  while textfile {
    found, line, right := split_from_left(textfile, #char "\n");
    textfile = right;
    if !found break;

    while true {
      val, success = parse_int(*line);
      if !success {
        if begins_with(line, "%") || !line {
          break;
        }
        print("Error. Invalid Integer\n");
        return;
      }

      if val == 0 {
        if array.count > 0 then {
          numvars = add_clauses(numvars, array, *clauses);
          array_reset(*array);
        }
      } else if val < 0 {
        l: Lit = NOT | (cast(Lit) (-val - 1));
        array_add(*array, l);
      } else {
        l: Lit = cast(Lit) (val - 1);
        array_add(*array, l);
      }
    }
  }

  solver.num_vars = numvars;
  solver.num_clauses = numclauses;
  solver.variables = NewArray(numvars, Var);
  solver.clauses   = clauses;
  return true;

  add_clauses :: (num_vars: int, array: [..] Lit, clauses: *[..] Clause) -> int {
    clause: Clause;

    if array.count <= 3 {
      numvars := array.count-1;
      for i: 0..numvars {
        clause[i] = array[i];
      }
      clause.count = cast(s32) array.count;
      array_add(clauses, clause);
    } else {
      lit := cast(Lit) num_vars;
      clause[0] = array[0];
      clause[1] = array[1];
      clause[2] = lit;
      clause.count = 3;
      array_add(clauses, clause);

      for i: 3..array.count-3 {
        clause[0] = NOT | lit;
        clause[1] = array[i];
        num_vars += 1;
        lit = cast(Lit) num_vars;
        clause[2] = lit;
        clause.count = 3;
        array_add(clauses, clause);
      }

      clause[0] = NOT | lit;
      clause[1] = array[array.count-2];
      clause[2] = array[array.count-1];
      clause.count = 3;
      array_add(clauses, clause);
    }

    return num_vars;
  }
}

Lit :: #type, distinct s32;
NOT : Lit : 0x8000_0000;

print_clause :: (arr: [] Lit) {
  print("(");
  for l, count: arr {
    sign := NOT & l;
    if sign == NOT then
      print(" !");
    else
      print(" ");

    l = ~NOT & l;
    print("x% ", l);
    if count < arr.count-1 then
      print("v");
  }
  print(")\n");
}

Solver :: struct {
  num_vars:    int;
  num_clauses: int;
  variables:   []   Var;
  clauses:     [..] Clause;
  learnt_clauses: [..] Clause;
}

Var :: enum u8 {
  False    ::    0;
  True     ::    1;
  Unassign :: 0xFF;
}

Clause :: struct {
  lit: [3] Lit;  
  count: s32;     // TODO: should we include more info?
}

operator [] :: inline (clause: Clause, index: int) -> Lit {
  return clause.lit[index];
}

operator []= :: inline (clause: *Clause, index: int, lit: Lit) {
  clause.lit[index] = lit;
}

#scope_file
#import "Basic";
#import "File";
#import "String";
