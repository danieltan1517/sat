main :: () {
  solver: Solver;
  open_cnf_file(*solver, "cnfs/uf20-03.cnf");
  //open_cnf_file(*solver, "cnfs/sat.cnf");
  //open_cnf_file(*solver, "cnfs/bcp.cnf");
  //open_cnf_file(*solver, "cnfs/unsat.cnf");
  //open_cnf_file(*solver, "cnfs/bcp2.cnf");
  for c: solver.clauses {
    print_clause(c);
  }
  print("number of variables: %\n", solver.num_vars);
  print("number of clauses: %\n", solver.num_clauses);
  sat := search(*solver);
  print("number of conflicts: %\n", solver.conflicts);
  if sat then {
    assert(verify(*solver));
    for var, count: solver.vars {
      print("x%1 = %2\n", count, var);
    }
    print("sat\n");
  } else {
    print("unsat\n");
  }
}

called := false;

open_cnf_file :: (solver: *Solver, filename: string) -> success: bool = false {
  assert(called == false, "Error. function called more than once.\n");
  textfile, success := read_entire_file(filename);
  if !success {
    return;
  }
  called = true;

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

  if array {
    print("Error. No zero at the end.\n");
    return;
  }

  solver.num_vars = numvars;
  solver.num_clauses = clauses.count;

  array_reserve(*solver.vars, (numvars * 5) / 4);
  for i: 0..numvars-1 {
    array_add(*solver.vars, .Unassign);
  }
  print("cnf count: %\n", solver.vars.count);
  solver.clauses   = clauses;
  return true;
}

add_clauses :: (num_vars: int, array: [..] Lit, clauses: *[..] Clause, $debug: bool = false) -> int {
  clause: Clause;
  if array.count <= 3 {
    numvars := array.count-1;
    for i: 0..numvars {
      clause[i] = array[i];
    }
    clause.count = cast(s32) array.count;
    array_add(clauses, clause);
    #if debug {
      print_clause(clause);
    }
  } else {
    lit := cast(Lit) num_vars;
    clause[0] = array[0];
    clause[1] = array[1];
    clause[2] = lit;
    clause.count = 3;
    array_add(clauses, clause);
    #if debug {
      print_clause(clause);
    }
    num_vars += 1;

    for i: 2..array.count-3 {
      clause[0] = NOT | lit;
      clause[1] = array[i];
      lit = cast(Lit) num_vars;
      num_vars += 1;
      clause[2] = lit;
      clause.count = 3;
      array_add(clauses, clause);
      #if debug {
        print_clause(clause);
      }
    }

    clause[0] = NOT | lit;
    clause[1] = array[array.count-2];
    clause[2] = array[array.count-1];
    clause.count = 3;
    array_add(clauses, clause);
    #if debug {
      print_clause(clause);
    }
  }

  return num_vars;
}

Lit :: #type, distinct s32;
NOT : Lit : 0x8000_0000;

print_clause :: (clause: Clause) {
  print("(");
  count := 0;
  while count < clause.count {
    l := clause[count];
    sign := NOT & l;
    if sign == NOT then
      print(" !");
    else
      print(" ");

    l = ~NOT & l;
    print("x% ", l);
    if count < clause.count-1 then
      print("v");
    count += 1;
  }
  print(")\n");
}

Solver :: struct {
  num_vars:       int;
  num_clauses:    int;
  level:          s32;
  vars:           [..] Var;
  clauses:        [..] Clause;
  learnt_clauses: [..] Clause;
  num_assigned:   int;
  trail:          [..] Path;
  conflicts:      int = 0;
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

for_expansion :: (clause: *Clause, body: Code, f: For_Flags) #expand {
  `it_index := 0;
  while it_index < clause.count {
    `it := clause.lit[it_index];
    #insert body;
    it_index += 1;
  }
}

operator [] :: inline (clause: Clause, index: int) -> Lit #expand {
  return clause.lit[index];
}

operator []= :: inline (clause: *Clause, index: int, lit: Lit) #expand {
  clause.lit[index] = lit;
}

Path :: struct {
  varnum: s32;
  clause: int;
  level:  s32;
  implied: bool;
  value: Var;
}

get_lit :: (l: Lit) -> Var, num: s32 {
  flag := (cast(Var) ((l & NOT) <<< 1)) ^ .True;
  num  := cast(s32) (l & (~NOT));
  return flag, num;
}

search :: (solver: *Solver) -> bool {
  array_reserve(*solver.trail, (3 * solver.num_vars) / 2);
  solver.level = 0;

  while true {
    stat := bcp(solver);
    if stat == .Conflict {
      print("Conflict.\n");
      // backtrack.
      level, clause := last_uip(solver);

      // unsat.
      if level < 0 || !clause then {
        return false;
      }

      num_vars := solver.num_vars;
      learnt_clauses := *solver.learnt_clauses;
      added := add_clauses(num_vars, clause, learnt_clauses, true);
      for 1..added-num_vars {
        array_add(*solver.vars, .Unassign);
      }
      solver.num_vars = added;
      solver.level = level;
      
      while solver.trail {
        path := solver.trail[solver.trail.count-1];
        solver.vars[path.varnum] = .Unassign;
        solver.num_assigned -= 1;
        //print("x% unassign\n", path.varnum);
        if path.level < solver.level
          break;
        pop(*solver.trail);
      }
      reset_temporary_storage();
      solver.conflicts += 1;
    } else {
      // solved.
      if solver.num_assigned >= solver.num_vars
        break;

      solver.level += 1;
      // choose another variable.
      choose(solver);
    }
  }

  return true;
}


rseed: u64 = 861097715;

random_int :: () -> u64 {
  rseed ^= rseed >> 12;
  rseed ^= rseed << 25;
  rseed ^= rseed >> 27;
  return rseed * 2685821657736338717;
}

verify :: (solver: *Solver) -> bool {
  for clause: solver.clauses {
    sat := false;
    for lit: clause {
      var, num := get_lit(lit);
      variable := solver.vars[num];
      if var == .False
        variable ^= .True;
      if variable == .True
        sat = true;
    }
    if sat == false
      return false;
  }
  return true;
}

last_uip :: (solver: *Solver) -> level: s32, clause: [..] Lit {
  level: s32 = -1;
  array: [..] Lit;
  array.allocator = temp;
  num_vars := solver.num_vars;
  for path: solver.trail {
    if !path.implied {
      if path.level < solver.level then {
        level = path.level;
      }
      
      l: Lit = cast(Lit) path.varnum;
      if path.value == .True {
        l |= NOT;
      } 

      array_add(*array, l);
    }
  }
  //print("level = %, %\n", level, array);
  return level, array;
}

choose :: (solver: *Solver) {
  num := cast(u64) solver.num_vars;
  r : u64 = 0xFFFF_FFFF_FFFF_FFFF;
  while true {
    r = (random_int() % num);
    if solver.vars[r] == .Unassign {
      solver.vars[r] = cast(Var) (random_int() & 1);
      path: Path;
      path.varnum = xx r;
      assert(path.varnum >= 0);
      path.clause = -1;
      path.level = solver.level;
      path.implied = false;
      path.value = solver.vars[r];
      print("Choose: x%1 = %2\n", path.varnum, path.value);
      array_add(*solver.trail, path);
      solver.num_assigned += 1;
      return;
    }
  }
}

bcp :: (solver: *Solver) -> BCP_Status {
  // TODO: watched literals.
  while true {
    TF := false;
    for clause, index: solver.clauses {
      if propagate_unit(solver, clause, index) == {
      case .Conflict;
        return .Conflict;
      case .Unit;
        TF = true;
      case .Good;
        // do nothing.
      }
    }
 
    for clause, index: solver.learnt_clauses {
      lindex := solver.clauses.count + index;
      if propagate_unit(solver, clause, lindex) == {
      case .Conflict;
        return .Conflict;
      case .Unit;
        TF = true;
      case .Good;
        // do nothing.
      }
    }
    if TF == false 
      break;
  }

  return .Good;

  propagate_unit :: (solver: *Solver, clause: Clause, clause_num: int) -> BCP_Status {
    num := clause.count-1;
    num_unassign := 0;
    index := -1;
    for i: 0..clause.count-1 {
      sign, var_num := get_lit(clause[i]);
      var := solver.vars[var_num];
      if var == .Unassign {
        num_unassign += 1;
        index = i;
      } else if var == sign {
        return .Good;
      }
    }

    if num_unassign > 1 {
      return .Good;
    } else if num_unassign == 1 {
      lit := clause[index];
      v, number := get_lit(lit);
      solver.vars[number] = v;
      solver.num_assigned += 1;
      path: Path;
      path.varnum = number;
      path.clause = clause_num;
      path.level = solver.level;
      path.implied = true;
      path.value = v;
      print("Imply x% = %\n", number, v);
      array_add(*solver.trail, path);
      return .Unit;
    } else {
      // conflict
      return .Conflict;
    }
  }
}

BCP_Status :: enum s8 {
  Conflict;
  Good;
  Unit;
}

#scope_file
#import "Basic";
#import "File";
#import "String";
