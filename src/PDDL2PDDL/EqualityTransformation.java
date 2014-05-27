package PDDL2PDDL;

import java.util.*;

import pddl4j.PDDLObject;
import pddl4j.RequireKey;
import pddl4j.Source;
import pddl4j.InvalidExpException;
import pddl4j.exp.*;
import pddl4j.exp.term.*;
import pddl4j.exp.action.*;
import pddl4j.exp.fcomp.*;
import pddl4j.exp.time.TimedExp;

class EqualityTransformation extends Transformation {
	static void transform(PDDLObject domain, PDDLObject problem) {
	
		// change requirments
	
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
			//todo: add durative actions support
			Action action = (Action) iter.next();
			Exp precondition = replaceEqualityOperator(action.getPrecondition(), eq_predicate);
			action.setPrecondition(precondition);
			Exp effect = replaceEqualityOperator(action.getEffect(), eq_predicate);
			action.setEffect(effect);
		}
		//todo: replace in goal
	}
}