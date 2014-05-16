import java.io.File;
import java.io.FileNotFoundException;
import java.util.*;

import pddl4j.ErrorManager;
import pddl4j.PDDLObject;
import pddl4j.Parser;
import pddl4j.RequireKey;
import pddl4j.Source;
import pddl4j.ErrorManager.Message;
import pddl4j.InvalidExpException;
import pddl4j.exp.AndExp;
import pddl4j.exp.OrExp;
import pddl4j.exp.AtomicFormula;
import pddl4j.exp.Exp;
import pddl4j.exp.ListExp;
import pddl4j.exp.ExpID;
import pddl4j.exp.InitEl;
import pddl4j.exp.Literal;
import pddl4j.exp.NotAtomicFormula;
import pddl4j.exp.NotExp;
import pddl4j.exp.term.Substitution;
import pddl4j.exp.term.Variable;
import pddl4j.exp.term.Term;
import pddl4j.exp.action.Action;
import pddl4j.exp.action.ActionDef;
import pddl4j.exp.action.AbstractActionDef;
import pddl4j.exp.action.ActionID;
import pddl4j.exp.fcomp.FCompExp;
import pddl4j.exp.fcomp.Comp;
import pddl4j.exp.QuantifiedExp;
import pddl4j.exp.ForallExp;
import pddl4j.exp.AbstractExp;
import pddl4j.exp.term.Constant;


class Pddl4pddl {
public static void main(String[] args) throws Exception {
	
    if (args.length != 3) {
        System.err.println("Invalid command line");
    } else {
        Parser parser = new Parser();
		
		PDDLObject domain = parser.parse(new File(args[1]));
		PDDLObject problem = parser.parse(new File(args[2]));
		PDDLObject obj = parser.link(domain, problem);
		
		ErrorManager mgr = parser.getErrorManager();
        if (mgr.contains(Message.ERROR)) {
            mgr.print(Message.ALL);
        } else {
            mgr.print(Message.WARNING);
            System.out.println("\nParsing domain done successfully ...");
            System.out.println("Parsing problem done successfully ...\n");
        }
		if (args[0].equals(":equality")) {
			transformEquality(domain, problem);
		} else if (args[0].equals(":disjunctive-preconditions")) {
			transformDisjunctivePreconditions(domain, problem);
		} else {
			System.err.println("Invalid command line");
		}
		
		System.out.println(problem.toString());
		System.out.println();
		System.out.println(domain.toString());
		
    }
}

static void transformDisjunctivePreconditions(PDDLObject domain, PDDLObject problem) {
	// change requirments

	String goal_predicate_name = "goal_predicate"; // This shpuld be unique
	
	List<InitEl> init = problem.getInit();
	AtomicFormula goal_predicate = new AtomicFormula(goal_predicate_name);
	domain.addPredicate(goal_predicate);
	
	Exp goal_exp = problem.getGoal();
	goal_exp = goal_exp.toDisjunctiveNormalForm();
	
	if (hasExp(goal_exp, ExpID.OR)) {
		problem.setGoal(goal_predicate);
		ListExp listExp = (ListExp) goal_exp;
		for (int i = 0; i < listExp.size(); i++) {
			Exp precondition = listExp.get(i);
			String action_name = "action_name" + i; //should be unique
			Action action = new Action(action_name);
			action.setEffect(goal_predicate);
			action.setPrecondition(precondition);
			domain.addAction(action);
		}
	}
}

static boolean hasExp(Exp e, ExpID id) {
	return false;
}

static void transformEquality(PDDLObject domain, PDDLObject problem) throws InvalidExpException {
	
	// change requirments:
	//for (Iterator<RequireKey> iter = problem.requirementsIterator(); iter.hasNext(); ) {
	//}
	// create unique name eq_predicate
	String eq_predicate = "eq"; // This shpuld be unique
	
	AtomicFormula eq_prdct = new AtomicFormula(eq_predicate);
	Constant o1 = new Constant("?o1");
	Constant o2 = new Constant("?o2");
	eq_prdct.add(o1);
	eq_prdct.add(o2);
	domain.addPredicate(eq_prdct);
	
	List<InitEl> init = problem.getInit();	
	for (Iterator<Constant> iter = problem.constantsIterator(); iter.hasNext(); ) {
		Constant object = iter.next();
		AtomicFormula predicate = new AtomicFormula(eq_predicate);
		predicate.add(object);
		predicate.add(object);
		init.add(predicate);
	}
	
	for (Iterator<ActionDef> iter = domain.actionsIterator(); iter.hasNext(); ) {
		Action action = (Action) iter.next();
		replaceEqualityOperator(action.getPrecondition(), eq_predicate);
	}
}

static void replaceEqualityOperator(Exp e, String eq_predicate) throws InvalidExpException {
	switch (e.getExpID()) {
    case AND: case OR:
        ListExp listExp = (ListExp) e;
		for (int i = 0; i < listExp.size(); i++) {
			if (listExp.get(i).getExpID().equals(ExpID.F_COMP)) {
				FCompExp fcomp3 = (FCompExp) listExp.get(i);
				if (fcomp3.getOp().equals(Comp.EQUAL) && fcomp3.getArg1().getExpID().equals(ExpID.TERM)
													  && fcomp3.getArg2().getExpID().equals(ExpID.TERM)) {											
					AtomicFormula predicate = new AtomicFormula(eq_predicate);
					predicate.add(fcomp3.getArg1());
					predicate.add(fcomp3.getArg2());
					listExp.set(i, predicate);
				}
			} else {
				replaceEqualityOperator(listExp.get(i), eq_predicate);
			}
		}
        break;
	case FORALL:
		ForallExp forall = (ForallExp) e;
		if (forall.getExp().getExpID().equals(ExpID.F_COMP)) {
			FCompExp fcomp1 = (FCompExp) forall.getExp();
			if (fcomp1.getOp().equals(Comp.EQUAL) && fcomp1.getArg1().getExpID().equals(ExpID.TERM)
												  && fcomp1.getArg2().getExpID().equals(ExpID.TERM)) {											
				AtomicFormula predicate = new AtomicFormula(eq_predicate);
				predicate.add(fcomp1.getArg1());
				predicate.add(fcomp1.getArg2());
				forall.setExp(predicate);
			}
		} else {
			replaceEqualityOperator(forall.getExp(), eq_predicate);
		}
		break;
    case NOT:
        NotExp notExp = (NotExp) e;
        if (notExp.getExp().getExpID().equals(ExpID.F_COMP)) {
			FCompExp fcomp2 = (FCompExp) notExp.getExp();
			if (fcomp2.getOp().equals(Comp.EQUAL) && fcomp2.getArg1().getExpID().equals(ExpID.TERM)
												  && fcomp2.getArg2().getExpID().equals(ExpID.TERM)) {											
				AtomicFormula predicate = new AtomicFormula(eq_predicate);
				predicate.add(fcomp2.getArg1());
				predicate.add(fcomp2.getArg2());
				notExp.setExp(predicate);
			}
		} else {
			replaceEqualityOperator(notExp.getExp(), eq_predicate);
		}
        break;
	case F_COMP:
		FCompExp fcomp2 = (FCompExp) e;
		if (fcomp2.getOp().equals(Comp.EQUAL) && fcomp2.getArg1().getExpID().equals(ExpID.TERM)
											  && fcomp2.getArg2().getExpID().equals(ExpID.TERM)) {											
			AtomicFormula predicate = new AtomicFormula(eq_predicate);
			predicate.add(fcomp2.getArg1());
			predicate.add(fcomp2.getArg2());
			//notExp.setExp(predicate);
		}
	case ATOMIC_FORMULA:        
        break;
    default:
        throw new InvalidExpException(e.getExpID());
    }
}


}