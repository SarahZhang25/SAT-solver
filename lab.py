#!/usr/bin/env python3
"""6.009 Lab 5 -- Boolean satisfiability solving"""

from shutil import move
import sys
import typing
import doctest

sys.setrecursionlimit(10000)
# NO ADDITIONAL IMPORTS


def satisfying_assignment(formula):
    """
    Find a satisfying assignment for a given CNF formula.
    Returns that assignment if one exists, or None otherwise.

    >>> satisfying_assignment([])
    {}
    >>> x = satisfying_assignment([[('a', True), ('b', False), ('c', True)]])
    >>> x.get('a', None) is True or x.get('b', None) is False or x.get('c', None) is True
    True
    >>> satisfying_assignment([[('a', True)], [('a', False)]])
    """
    def build_internal_formula_repr():
        """
        Returns an internal formula representation: a list of dictionaries, where each dictionary represents a clause, 
        with key value pairs being the variable and its associated Boolean value, respectively
        """
        repr = []
        for clause in formula:
            # new dictionary representation of clause
            new_clause = {}
            for literal in clause:
                if literal[0] in new_clause and new_clause[literal[0]] != literal[1]:
                    # if a var has both True and False, then it's always satisfied and we don't need to add it to the clause
                    new_clause.pop(literal[0])
                else:
                    new_clause[literal[0]] = literal[1]
            if new_clause != {}: # and not ignore:
                # if new_clause == {}, then it is a fully satisfied clause already
                repr.append(new_clause)
        return repr

    def update_formula(formula, var, var_assignment):
        """
        Returns a new formula that has been updated after a given variable assignment

        Arguments:
            formula: internal representation of a CNF formula
            var: string, variable to eliminate/reduce upon
            var_assignment: Boolean of what to evaluate the var as
        
        Returns:
            A new, updated CNF formula
        """
        new_formula = []
        for i in range(len(formula)):
            new_clause = formula[i].copy()
            if var in formula[i]: # need to modify clause
                # if var_assignment IS NOT equal what is in input formula, remove the literal from the clause 
                # if var_assignment IS equal to what is in input formula, do not further consider the clause
                if formula[i][var] != var_assignment:
                    new_clause.pop(var)
                    new_formula.append(new_clause)
            else: # take entire clause
                new_formula.append(new_clause)
        return new_formula

    def update_soln(soln, var, var_assignment):
        """
        Returns a new solution dictionary that has been updated after a given variable assignment

        Arguments:
            formula: internal representation of a CNF formula
            var: string, variable to eliminate/reduce upon
            var_assignment: Boolean of what to evaluate the var as
        
        Returns:
            A new, updated solution dictionary
        """
        new_soln = soln.copy()
        new_soln[var] = var_assignment
        return new_soln

    def get_unit_clause(formula):
        """
        Returns the first unit clause in the formula, or None if there are none

        Arguments:
            formula: internal representation of a CNF formula

        Returns:
            A tuple of the first unit clause in the formula, None if no unit clauses exist
        """
        for clause in formula:
            if len(clause) == 1:
                return next(zip(clause.keys(), clause.values())) # the var:bool pair in the clause
        return None # no unit clause found

        
    def solve_cnf(formula, soln, var, var_assignment):
        """
        Solves a CNF formula by recursively assigning variables

        Arguments:
            formula: internal representation of a CNF formula
            soln: solution dictionary
            var: string, variable to eliminate/reduce upon
            var_assignment: Boolean of what to evaluate the var as

        Returns:
            A solution dictionary of assignments that satisfy the formula if it is satisfiable, else
            None is the formula is not satisfiable
        """
        # evalute base cases
        if formula == []: # solved state
            return soln
        elif {} in formula: # formula unsolvable
            return None
        else: # recursve on remaining options
            # apply the var and var_assignment to the formula
            updated_formula = update_formula(formula, var, var_assignment)
            updated_soln = update_soln(soln, var, var_assignment)

            if updated_formula == []: # solved state
                return updated_soln
            elif {} in updated_formula: # formula unsolvable
                pass
            else: #recurse
                # try to target unit clauses first
                unit_clause = get_unit_clause(updated_formula)
                if unit_clause: # exists
                    # print("unit exists:", updated_formula, updated_soln, unit_clause)
                    attempt = solve_cnf(updated_formula, updated_soln, unit_clause[0], unit_clause[1])
                    if attempt: # return if exists
                        return attempt
                else: 
                    next_var = list(updated_formula[0])[0] # choose the first var that shows up in the formula
                    next_assignment = updated_formula[0][next_var]
                    
                    # print("at:", updated_formula, updated_soln, next_var)
                    attempt = solve_cnf(updated_formula, updated_soln, next_var, next_assignment)
                    if attempt:
                        return attempt

                    # try other choice for var
                    attempt = solve_cnf(updated_formula, updated_soln, next_var, not next_assignment)
                    if attempt:
                        return attempt

                # if neither worked, this line of recursion failed, do nothing more (backtrack)

    # main function body
    formula = build_internal_formula_repr()
    if formula == []:
        return {}
    
    move = get_unit_clause(formula) # try to start with removing a unit clause
    if move: # if unit clause exists
        return solve_cnf(formula, {}, move[0], move[1])
    else:
        var = list(formula[0])[0]
        assignment = formula[0][var]

        soln1 = solve_cnf(formula, {}, var, assignment)
        if soln1:
            return soln1
        soln2 = solve_cnf(formula, {}, var, not assignment)
        if soln2:
            return soln2

        return None # no assignment satisfies cnf


def boolify_scheduling_problem(student_preferences, room_capacities):
    """
    Convert a quiz room scheduling problem into a Boolean formula.

    student_preferences: a dictionary mapping a student name (string) to a list
                         of room names (strings) that work for that student

    room_capacities: a dictionary mapping each room name to a positive integer
                     for how many students can fit in that room

    Returns: a CNF formula encoding the scheduling problem, as per the
             lab write-up

    We assume no student or room names contain underscores.
    """

    def make_var(student_name, room_name):
        """
        Returns a string in the format of "<student_name>_<room_name>"
        """
        return student_name + "_" + room_name

    def n_choose_k_indices(n, k):
        """
        Wrapper function for n_choose_k that returns all possible subsets 
        of size k in set of 1, ..., n

        Arguments:
            n: int, desired set size
            k: int, desired subset size

        Returns:
            list of lists of indices (inner list represents a subset)
        """
        def n_choose_k(n, k, combos):
            """
            Recursive function that returns all possible subsets of 
            size k in set of 1, ..., n
            """
            if k == 1:
                return combos
            else:
                new_combos = []
                for subset in combos:
                    for j in range( subset[-1]+1, n-k+2 ):
                        new_combos.append(subset + [j])
                return n_choose_k(n, k-1, new_combos)    

        return n_choose_k(n, k, [[i] for i in range(n-k+2)])

    def n_choose_k_values(values, combos_indices):
        """
        Returns a list of subsets of given values given the indicies of the elements of each subset.

        Arguments:
            values: list of values
            combos_indices: list of list of combinations to evaluate

        Returns:
            list of lists of values (inner list represents a subset)
        """
        results = []
        for item in combos_indices:
            results.append([values[i] for i in item])
        return results

    def student_preferences_rule(student_preferences):
        """
        Returns a CNF formula that represents the student preferences rule

        Arguments:
            student_preferences: a dictionary mapping a student name (string) to a list
                        of room names (strings) that work for that student

        Returns:
            CNF formula
        """
        formula = [] 
        for stud in student_preferences:
            clause = []
            for room in student_preferences[stud]:
                clause.append((make_var(stud, room), True))
            formula.append(clause)
        return formula

    def one_student_per_room_rule(students, rooms):
        """
        Returns CNF formula that represents the one student per room rule

        Arguments:
            students: list of student names
            rooms: list of room names

        Returns:
            CNF formula
        """
        # each student must be in at least one room --> satisfied by student_preferences_rule
        # each student must be in at most one room
        formula = []
        pairs = n_choose_k_values(rooms, n_choose_k_indices(len(rooms), 2))
        for student in students:
            for pair in pairs:
                clause = [(make_var(student, room), False) for room in pair]
                formula.append(clause)
        return formula

    def room_capacities_rule(students, room_capacities):
        """
        Returns a CNF formula that represents the room capacities rule

        Arguments:
            students: list of student names
            room_capacities: a dictionary mapping each room name to a positive integer
                        for how many students can fit in that room input dictionary
        
        Returns:
            CNF formula
        """
        formula = []
        for room in room_capacities:
            if room_capacities[room] == 0: # generate size 1 subsets using each student
                student_subsets = n_choose_k_values(students, [[i] for i in range(len(students))])
            elif room_capacities[room] < len(students): # generate N+1 size subsets
                student_subsets = n_choose_k_values(students, n_choose_k_indices(len(students), room_capacities[room]+1))
            else: # if capacity >= num students, room can fit any number of students so do not need to include in formula
                continue

            for combo in student_subsets:
                clause = [(make_var(student, room), False) for student in combo]
                formula.append(clause)
        return formula

    # main function body
    formula = student_preferences_rule(student_preferences) + \
                one_student_per_room_rule(list(student_preferences), list(room_capacities)) + \
                room_capacities_rule(list(student_preferences), room_capacities)
    return formula

if __name__ == '__main__':
    import doctest
    _doctest_flags = doctest.NORMALIZE_WHITESPACE | doctest.ELLIPSIS
    doctest.testmod(optionflags=_doctest_flags)

    # student_prefs = {'Alice': {'basement', 'penthouse'},
    #                         'Bob': {'kitchen'},
    #                         'Charles': {'basement', 'kitchen'},
    #                         'Dana': {'kitchen', 'penthouse', 'basement'}}
    # room_caps = {'basement': 1,
    #                         'kitchen': 2,
    #                         'penthouse': 4}
    # pp.pprint(room_capacities_rule(list(student_prefs), room_caps))
    # pp.pprint(one_student_per_room_rule(list(student_prefs), list(room_caps)))
    # print(student_preferences_rule({'Alice': {'basement', 'penthouse'}, 'Bob': {'kitchen'}, 'Charles': {'basement', 'kitchen'}, 'Dana': {'kitchen', 'penthouse', 'basement'}} ))
    # n = 6
    # k = 3
    # combos = n_choose_k(n, k, [[i] for i in range(n-k+2)])
    # pp.pprint(combos)

    # C_sch = [{"student0": ["session0", "session2", "session3", "session4", "session6", "session8"], "student1": ["session1", "session3", "session6", "session7"], "student7": ["session1", "session2", "session3", "session4", "session5", "session9"], "student4": ["session1", "session2", "session5", "session6", "session7", "session9"], "student3": ["session5"], "student2": ["session2", "session3", "session4", "session5", "session7"], "student9": ["session0", "session1", "session5", "session6", "session9"], "student6": ["session1", "session2", "session5", "session6", "session8"], "student8": ["session0", "session2", "session3", "session7", "session8", "session9"], "student5": ["session0", "session7", "session8"]}, {"session6": 1, "session8": 4, "session1": 3, "session2": 0, "session9": 3, "session7": 6, "session0": 3, "session5": 0, "session3": 7, "session4": 2}]
    # formula = boolify_scheduling_problem(*C_sch)
    # print(satisfying_assignment(formula))

    # student_preferences = {"Alice": ["session1", "session2"], "Bob": ["session3"], "Charles": ["session3"]}
    # room_capacities = {"session1": 1, "session2": 1, "session3": 3}
    # formula = boolify_scheduling_problem(student_preferences, room_capacities)
    # print(satisfying_assignment(formula))

    # rule1 = [[('saman', True), ('mike', True), ('charles', True),
    #       ('jonathan', True), ('tim', True)]]

    # rule4 = [[('saman', False), ('pickles', True)],
    #      [('saman', False), ('chocolate', False)],
    #      [('saman', False), ('vanilla', False)]]

    # ex = [
    # [('a', True), ('b', True), ('c', True)],
    # [('a', False), ('f', True)],
    # [('d', False), ('e', True), ('a', True), ('g', True)],
    # [('h', False), ('c', True), ('a', False), ('f', True)],
    # ]

    # c = [["a", True], ["a", False]],[["b", True], ["a", True]],[["b", True]],[["b", False],["b", False],["a", False]], [["c",True],["d",True]], [["c",True],["d",True]]
    # # need to modify my internal representation s.t. if a var appears in a clause twice like in [["a", True], ["a", False]], then it doesn't include the var at all
    # # since any choice for that var will satisfy 

    # cnf1 = [[("a",True), ("b",True)], [("a",False), ("b",False), ("c",True)],
    #        [("b",True),("c",True)], [("b",True),("c",False)]]
    
    # pp.pprint(cnf1)
    
    # pp.pprint(satisfying_assignment(cnf1))
    
    # ex_repr = internal_formula_repr(ex)
    # pp.pprint(ex_repr)
    # ex_repr = update_formula(ex_repr, 'a', True)
    # ex_repr = update_formula(ex_repr, 'f', False)
    # pp.pprint(ex_repr)
    # print({} in ex_repr)
