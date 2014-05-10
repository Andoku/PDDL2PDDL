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
		} else {
			System.err.println("Invalid command line");
		}
		
		System.out.println(problem.toString());
		System.out.println();
		System.out.println(domain.toString());
		
    }
}

static void transformEquality(PDDLObject domain, PDDLObject problem) throws InvalidExpException {
	
	//for (Iterator<RequireKey> iter = problem.requirementsIterator(); iter.hasNext(); ) {
	//	
	//}
	
	List<InitEl> init = problem.getInit();
	AtomicFormula prdct1 = new AtomicFormula("eq");
	Constant o1 = new Constant("?o1");
	Constant o2 = new Constant("?o2");
	prdct1.add(o1);
	prdct1.add(o2);
	domain.addPredicate(prdct1);	
	for (Iterator<Constant> iter = problem.constantsIterator(); iter.hasNext(); ) {
		Constant object = iter.next();
		AtomicFormula predicate = new AtomicFormula("eq");
		predicate.add(object);
		predicate.add(object);
		init.add(predicate);
	}
	
	for (Iterator<ActionDef> iter = domain.actionsIterator(); iter.hasNext(); ) {
		Action action = (Action) iter.next();
		System.out.println(action.getPrecondition().toString());
		replaceEqulityOperator(action.getPrecondition());
	}
}

static void replaceEqulityOperator(Exp e) throws InvalidExpException {
	switch (e.getExpID()) {
    case AND:
        AndExp andExp = (AndExp) e;
		for (int i = 0; i < andExp.size(); i++) {
			if (andExp.get(i).getExpID().equals(ExpID.F_COMP)) {
				FCompExp fcomp3 = (FCompExp) andExp.get(i);
				if (fcomp3.getOp().equals(Comp.EQUAL) && fcomp3.getArg1().getExpID().equals(ExpID.TERM)
													  && fcomp3.getArg2().getExpID().equals(ExpID.TERM)) {											
					AtomicFormula predicate = new AtomicFormula("eq");
					predicate.add(fcomp3.getArg1());
					predicate.add(fcomp3.getArg2());
					andExp.set(i, predicate);
				}
			} else {
				replaceEqulityOperator(andExp.get(i));
			}
		}
        break;
    case ATOMIC_FORMULA:        
        break;
	case FORALL:
		ForallExp forall = (ForallExp) e;
		if (forall.getExp().getExpID().equals(ExpID.F_COMP)) {
			FCompExp fcomp1 = (FCompExp) forall.getExp();
			if (fcomp1.getOp().equals(Comp.EQUAL) && fcomp1.getArg1().getExpID().equals(ExpID.TERM)
												  && fcomp1.getArg2().getExpID().equals(ExpID.TERM)) {											
				AtomicFormula predicate = new AtomicFormula("eq");
				predicate.add(fcomp1.getArg1());
				predicate.add(fcomp1.getArg2());
				forall.setExp(predicate);
			}
		} else {
			replaceEqulityOperator(forall.getExp());
		}
		break;
	case OR:
		OrExp orExp = (OrExp) e;
        for (int i = 0; i < orExp.size(); i++) {
			if (orExp.get(i).getExpID().equals(ExpID.F_COMP)) {
				FCompExp fcomp4 = (FCompExp) orExp.get(i);
				if (fcomp4.getOp().equals(Comp.EQUAL) && fcomp4.getArg1().getExpID().equals(ExpID.TERM)
													  && fcomp4.getArg2().getExpID().equals(ExpID.TERM)) {											
					AtomicFormula predicate = new AtomicFormula("eq");
					predicate.add(fcomp4.getArg1());
					predicate.add(fcomp4.getArg2());
					orExp.set(i, predicate);
				}
			} else {
				replaceEqulityOperator(orExp.get(i));
			}
		}
		break;
    case NOT:
        NotExp notExp = (NotExp) e;
        if (notExp.getExp().getExpID().equals(ExpID.F_COMP)) {
			FCompExp fcomp2 = (FCompExp) notExp.getExp();
			if (fcomp2.getOp().equals(Comp.EQUAL) && fcomp2.getArg1().getExpID().equals(ExpID.TERM)
												  && fcomp2.getArg2().getExpID().equals(ExpID.TERM)) {											
				AtomicFormula predicate = new AtomicFormula("eq");
				predicate.add(fcomp2.getArg1());
				predicate.add(fcomp2.getArg2());
				notExp.setExp(predicate);
			}
		} else {
			replaceEqulityOperator(notExp.getExp());
		}
        break;
    default:
        throw new InvalidExpException(e.getExpID());
    }
}

}