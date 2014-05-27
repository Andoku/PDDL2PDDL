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

class UniversalPreconditionsTransformation extends Transformation {
	
	static void transform(PDDLObject domain, PDDLObject problem) {
		for (Iterator<ActionDef> iter = domain.actionsIterator(); iter.hasNext(); ) {
			//todo: add durative actions support
			Action action = (Action) iter.next();
			Exp precondition = replaceForall(action.getPrecondition(), problem);
			action.setPrecondition(precondition);
			Exp effect = replaceForall(action.getEffect(), problem);
			action.setEffect(effect);
		}
		//todo: replace in goal
	}
}