#include "utilities.hh"
#include <sys/timeb.h>
#include <queue> 
#include<ctime>
using namespace std;

extern string cex_prefix;  
extern bool *satisfied;
extern unsigned int num_of_satisfied;
bool is_valid_state(BDD state, vector<BDD> v);
 //double c_end, c_start;

void 
do_model_checking(bdd_parameters * para)
{
  if (options["quiet"] == 0 && options["uniform"] == 0)
    cout << "Checking formulae..." << endl;

  BDD fair_reach;
  BDD in_st = *(para->in_st);
        
  struct timeb tmb_mc, tmb_mc1;
  if(options["verbosity"] > 1) 
    ftime(&tmb_mc);
    
  string str = "_init";
  (*is_evaluation)[str] = is_istates;
  modal_formula *init = new modal_formula(new atomic_proposition(&str));

  if (!is_fairness->empty()) {
		if(para->fair_gamma_FO != NULL) {
			for(map<string, BDD*>::iterator it = para->fair_gamma_FO->begin(); it != para->fair_gamma_FO->end(); it++) 
				delete it->second;
			delete para->fair_gamma_FO;
			para->fair_gamma_FO = NULL;
		}
		if(para->nfair_gamma_FO != NULL) {
			for(map<string, BDD*>::iterator it = para->nfair_gamma_FO->begin(); it != para->nfair_gamma_FO->end(); it++) 
				delete it->second;
			delete para->nfair_gamma_FO;
			para->nfair_gamma_FO = NULL;
		}
    if ((options["quiet"] == 0 || options["simulation"] == 0) && options["uniform"]==0)
      cout << "Building set of fair states..." << endl;
    for (vector< fairness_expression * >::iterator i =
           is_fairness->begin(); i != is_fairness->end(); i++) {
      BDD fairset = (*i)->check_formula(para);
      (*i)->set_bdd_representation(fairset);
    }
    // This is a set of "fair" states (the beginning of a fair computation)
    fair_reach = check_EG_fair(para->bddmgr->bddOne(), para);
    delete para->reach;
    para->reach = new BDD(fair_reach);
    in_st *= fair_reach;
  }       // end if
  (*para->BDD_cache)["_init"] = in_st;

  vector< vector< int >*> *countex = new vector< vector< int >*>;
  map< int, BDD * > *idbdd = new map< int, BDD * >;
  vector< vector< transition * >*> *cextr = new vector< vector< transition * >*>;

  if ((options["quiet"] == 0 || options["simulation"] == 0) && options["uniform"] == 0)
    cout << "Verifying properties..." << endl;

  // Check if fair_reach is empty bdd
  if (!is_fairness->empty() && fair_reach == para->bddmgr->bddZero()){
    if (options["quiet"] == 0)
      cout << "  Warning: ";
    cout << "The fairness constraint does not hold in any paths." << endl;
  }

  char buff[20];
  for (unsigned int i = 0; i < is_formulae->size(); i++){
    struct timeb tmb_formula, tmb_formula1;
    if(options["verbosity"] > 1) 
      ftime(&tmb_formula);

    if(satisfied[i] /*&& options["debug"] == 0*/)
      continue;
    set< string > trans_set;
    scount = 0;
    bool satisfaction = false;
    modal_formula f(4, init, &((*is_formulae)[i]));
    BDD result = f.check_formula(para);

 //cout<<" details result of formula"<<endl;
 //Cudd_PrintDebug(para->bddmgr->getManager(), result.getNode(), 2, 4);
/*************test***********************/

/*

for (map< string, bool_expression * >::iterator i = is_evaluation->begin();
         i != is_evaluation->end(); i++){
         c++;
         if(c >= 6)
          cout<<i->first<<endl;
          namesAtm.push_back(i->first);
          bool_expression *simple = i->second;
          BDD P = simple->encode_bdd_flat(para, para->bddmgr->bddOne());
          atmprops.push_back(P);
          }
       basic_agent *agent = (*agents)[1];
       set< string > *ag_act = agent->get_actions();
       cout<<ag_act->size()<<"  HEYYYY"<<endl;

//c_start = clock();
*/
/*
bool_expression *simple4 = is_evaluation->find("q1")->second;
BDD P5 = simple4->encode_bdd_flat(para, para->bddmgr->bddOne());
//BDD P5 = p5*(*para->reach);
bool_expression *simple5 = is_evaluation->find("q2")->second;
BDD P6 = simple5->encode_bdd_flat(para, para->bddmgr->bddOne());
//BDD P6 = p6*(*para->reach);
bool_expression *simple0 = is_evaluation->find("paid")->second;
BDD P1 = simple0->encode_bdd_flat(para, para->bddmgr->bddOne());
//BDD P1 = p1*(*para->reach);
bool_expression *simple1 = is_evaluation->find("ticket")->second;
BDD P2 = simple1->encode_bdd_flat(para, para->bddmgr->bddOne());
//BDD P2 = p2*(*para->reach);
bool_expression *simple2 = is_evaluation->find("selected")->second;
BDD P3 = simple2->encode_bdd_flat(para, para->bddmgr->bddOne());
//BDD P3 = p3*(*para->reach);
bool_expression *simple3 = is_evaluation->find("error")->second;
BDD P4 = simple3->encode_bdd_flat(para, para->bddmgr->bddOne());
//BDD P4 = p4*(*para->reach);
vector<BDD> results = {P1,P2,P3,P4,P5,P6};
vector<BDD> *res = &results;
//BDD form = *para->reach;
BDD form = P1*P2 + !P1*P2;
BDD form1 = ExistAbstractProp(P5, form, res, para);
//vector<BDD> resultt =  Mintermsform(form,res,para);
//cout<< " 28/06/2022 "<< resultt.size()<< endl;
//BDD result2 =

*/
/*
  struct timeb tmb2;
  ftime(&tmb2);
int m = cmplxformProp(form,res,para);
    struct timeb tmb3;
    ftime(&tmb3);
      cout << "  complexity of proposition equals " << m << endl;
    cout << "execution time of complexity algorithm =  " << ((tmb3.time-tmb2.time) + (tmb3.millitm-tmb2.millitm)/1000.0) << endl;

*/
/*
 if (m == -1){
 cout<<"There is no natural strategy"<<endl;
 }
 else{
 cout<< "The complexity of z is "<<m<<endl;
 } */
//BDD AllStates = para->bddmgr->bddZero();
//vector<BDD> * w = para->v;
 //for (unsigned int j = 0; j < w->size() ; j++){
   // AllStates = AllStates + (*w)[j];
    //}
  //

//cmplxNatStr(BDD q1, BDD q2,vector<BDD> * res, string grpname, bdd_parameters * para)


//int m = cmplxNatStr(para->bddmgr->bddOne(), resultt, res , "g1" , para);
//cout<<" the complexity of the natural strategy to reach ticket is "<< m <<endl;
//modal_formula f0(4, init, &((*is_formulae)[0]));
//BDD result0 = f0.check_formula_Nat(para);
//cout<< " details P1 "<<endl;
//Cudd_PrintDebug(para->bddmgr->getManager(), resultt.getNode(), 2, 4);
//cout<<" details result0 "<<endl;
//Cudd_PrintDebug(para->bddmgr->getManager(), result0.getNode(), 2, 4);
//if(result0 == P1)cout<<" YESS"<<endl;
//BDD res11 = !in_st * (*para->reach);
//BDD res22 = P3  * (*para->reach);
//BDD res12 = (!in_st + P3 ) * (*para->reach);
//cout<<"The results of in_st"<<endl;
//Cudd_PrintDebug(para->bddmgr->getManager(), res11.getNode(), 2, 4);
//cout<<"The results of error"<<endl;
//Cudd_PrintDebug(para->bddmgr->getManager(), res22.getNode(), 2, 4);
//if (res12 == result ){cout<<" P3 is equal to result "<<endl;}
/*
bool_expression *simple01 = is_evaluation->find("paid")->second;
BDD P01 = simple01->encode_bdd_flat(para, para->bddmgr->bddOne()) * (*para->reach);

BDD P02 = P01 * (*para->reach);


    modal_formula f0(4, init, &((*is_formulae)[0]));
    BDD resultt0 = f0.check_formula(para);

    if (P02 == resultt0)
    cout<<"Yes they are equal"<<endl;
     Cudd_PrintDebug(para->bddmgr->getManager(), P0.getNode(), 2, 4);
     Cudd_PrintDebug(para->bddmgr->getManager(), P01.getNode(), 2, 4);
     Cudd_PrintDebug(para->bddmgr->getManager(), P02.getNode(), 2, 4);
     Cudd_PrintDebug(para->bddmgr->getManager(), resultt0.getNode(), 2, 4);


    modal_formula f0(4, init, &((*is_formulae)[0]));
    BDD result0 = f0.check_formula(para);
    modal_formula f1(4, init, &((*is_formulae)[1]));
    BDD result1 = f1.check_formula(para);
    modal_formula f2(4, init, &((*is_formulae)[2]));
    BDD result2 = f2.check_formula(para);
    modal_formula f3(4, init, &((*is_formulae)[3]));
    BDD result3 = f3.check_formula(para);

*/


//BDD resultt = P0*P1*P2*P3;
/*
    BDD PR = P0 * (*para->reach);

    if(P0 * (*para->reach) == resultt0 )
    cout<<" They are equal"<<endl;
    else cout<<"Noooo"<<endl;
      //   int natsize = 0;
       //natsize = cmplxNatStr(para->bddmgr->bddOne(), phi1, name, para);
       //cout <<  "The complexity of natural strategy is "<< natsize << endl;

//bool_expression *simple = is_evaluation->find("p1win")->second;
//BDD result3 = simple->encode_bdd_flat(para, para->bddmgr->bddOne()) * (*para->reach);

  vector<BDD> * w = para->v;
  BDD x_1 = (*w)[0];
  BDD x_2 = (*w)[1];
  BDD x_3 = (*w)[2];
  BDD x_4 = (*w)[3];
  BDD x_5 = (*w)[4];
  BDD x_6 = (*w)[5];
 BDD  z =    x_1 * x_2 + x_3;
 BDD temp1;
 BDD temp2;
 BDD temp3;
 //DdGen *gen;
 //CUDD_VALUE_TYPE gvalue;
 // int *gcube;
 // vector<BDD>  var; */



  /*int n=0;

        DdGen *gen;
      CUDD_VALUE_TYPE gvalue;
      int *gcube;
      int aa = 0;

    cout<< " The method Cudd_ForeachCube "<<endl;
      cout<<" start iterationing through cubes "<<endl;

      Cudd_ForeachCube(para->bddmgr->getManager(),z.getNode(),gen,gcube,gvalue){
cout <<  "iterating through cubes "<<endl;
//cout<< " the value of gcube is "<< gcube<<endl;

  }
*/



/*

    for (unsigned int j = 0; j < results.size() - 1 ; j++){
    temp3 = results[j];
    temp1 = !temp3 * results[2];
    temp2 = temp3 * results[2];
    if(temp1 == para->bddmgr->bddZero()){
   //      var = var.push_back((*w)[j]);
         m++;
        }else if( temp2 == para->bddmgr->bddZero()){
     //    var = var.push_back((*w)[j]);
         m++;
         n++;
        }
  }

*/
/*************Algorithm to find the complexity of a cube of atomic prop   *********

  for (unsigned int j = 0; j < w->size(); j++){
    temp1 = !(*w)[j] * z;
    temp2 = (*w)[j] * z;
    if(temp1 == para->bddmgr->bddZero()){
   //      var = var.push_back((*w)[j]);
         m++;
        }else if( temp2 == para->bddmgr->bddZero()){
     //    var = var.push_back((*w)[j]);
         m++;
         n++;
        }
  }

 cout<< " The cube z has "<<m<<" number of atomic propositions "  << m-1 << " multiplications and "<< n <<"  negations "<<endl;



*/

 //Cudd_PrintDebug(para->bddmgr->getManager(), result.ExistAbstract((*w)[j]).getNode(), 2, 4);
  //cout<< " result print " <<endl;
//Cudd_PrintDebug(para->bddmgr->getManager(), result.getNode(), 2, 4);
/*cout<< "Testing the complexity of the formula"<<endl;
      BDD x = para->bddmgr->bddVar();
      BDD y = para->bddmgr->bddVar();
      //BDD z = para->bddmgr->bddVar();
      DdGen *gen;
      CUDD_VALUE_TYPE gvalue;
      int *gcube;
      int aa = 0;

      Cudd_ForeachCube(para->bddmgr->getManager(),z.getNode(),gen,gcube,gvalue){
cout <<  "iterating through cubes "<<endl;
  }**/

 /* for (unsigned int j = 0; j < w->size(); j++){

    if( result.ExistAbstract((*w)[j]) != result){
            aa++;
        }
  }
    cout << "Support size of the result using manual method is " << aa << endl;
   cout <<  "Support size of the result is "<<  Cudd_SupportSize(para->bddmgr->getManager(), result.getNode()) << endl;
   cout <<  "Support size of the formula x is "<<  Cudd_SupportSize(para->bddmgr->getManager(), x.getNode()) << endl;
   cout <<  "Support size of the formula z is "<<  Cudd_SupportSize(para->bddmgr->getManager(), z.getNode()) << endl; **/
/*********************endtest************************************/
    satisfaction = result == *para->reach;
    satisfied[i] = satisfaction;
    num_of_satisfied = satisfaction? num_of_satisfied+1 : num_of_satisfied;
    if(options["uniform"] == 0) {
      if (options["quiet"] == 0)
        cout << "  Formula number " << i+1 << ": " <<
          (*is_formulae)[i].to_string() << ", is " << (satisfaction ? "TRUE" : "FALSE")
             << " in the model" << endl;
      else
        cout << (satisfaction ? "TRUE" : "FALSE") << endl;
    }

    if ((options["cex"] >= 1)) {
      // Computing counterexample / witness
      BDD *is = new BDD(in_st);
      
      scount = 0;
      
      modal_formula *g = options["uniform"] == 1 ? NULL : (*is_formulae)[i].push_negations(0);

      string str_head;
      bool done = false;
      bool hascex = false;

      if (satisfaction && options["uniform"] == 1) {
        hascex = true;
        str_head = "statespace";
        
				scount = export_model(para, is, countex, idbdd, cextr);
				if(scount > 0)
					done = true;
      } else if ((satisfaction) && !(g->is_NonTemporal()) && (g->is_ECTLK_new())) {
        // True and ECTLK: can print witness
        hascex = true;
        str_head = "witness";
  
        if (options["quiet"] == 0)
          cout << "  The following is a witness for the formula: " << endl;
  
        while ((*is) != para->bddmgr->bddZero()) {
          BDD curinitstate = is->PickOneMinterm(*para->v);
    
          if (is_valid_state(curinitstate, *para->v)) {
            bool cexresult = g->build_cex(&curinitstate, 0, para, countex, idbdd, cextr);
            if (cexresult) {
              done = true;
              break;
            } else {
              *is = *is - curinitstate;
              scount = 0;
              clear_cex(countex, idbdd, cextr);
            }
          }
        }
      } else if (!satisfaction && options["uniform"] == 0) {
        // False and ACTLK: can print counterexample
        if (options["quiet"] == 0)
          cout <<
            "  The following is a counterexample for the formula: " << endl;
        hascex = true;
        str_head = "counterexample";
  
        *is = *is - result;
        if(g->is_ACTLK_new()) {
          // Negation of the formula:
          modal_formula fcex1(3, g);
          modal_formula *fcex = fcex1.push_negations(0);
          //cout << "fcex = " << fcex->to_string() << endl;
          while (*is != para->bddmgr->bddZero()) {
            BDD curinitstate = is->PickOneMinterm(*para->v);
            //print_state(curinitstate, *v);

            if (is_valid_state(curinitstate, *para->v)) {
              bool cexresult = fcex->build_cex(&curinitstate, 0, para, countex, idbdd, cextr);
              if (cexresult) {
                done = true;
                break;
              } else {
                *is = *is - curinitstate;
                scount = 0;
                clear_cex(countex, idbdd, cextr);
              }
            }
          }
          if(fcex != &fcex1)
            delete fcex;
        } else {
          done = true;
          BDD init_state = is->PickOneMinterm(*para->v);
          idbdd->insert(pair < int, BDD * >(0, new BDD(init_state)));
          vector< int >desc;    
          desc.push_back(0);
          countex->push_back(new vector< int >(desc));  
        }
      } else if (satisfaction) {
        if (options["quiet"] == 0)
          cout <<
            "    -- Sorry it is not possible to compute witnesses for non-ECTLK formulae"
               << endl;
      } 
  
      if(hascex) {
        if (!done) {
          if (options["quiet"] == 0) {
            cout <<
              "A " << str_head << " exists but could not be generated." << endl;
          }
        } else {
          if (options["cex"] == 1 || options["cex"] == 3) {
            for (int ac = 0; ac < (int) countex->size(); ac++) {
              cout << "   < ";
              for (int j = 0; j < (int) countex->at(ac)->size(); j++) {
                cout << countex->at(ac)->at(j) << " ";
              }
              cout << "> " << endl;
            }
      
            cout << "  States description: " << endl;
            for (map< int, BDD * >::iterator iter =
                   idbdd->begin(); iter != idbdd->end(); iter++) {
        
              cout << "------------- State: " << iter->first << " -----------------" << endl;
              print_state(*iter->second, *para->v);
              cout << "----------------------------------------" << endl;
            }
          }
          if (options["cex"] == 2 || options["cex"] == 3) {
						sprintf(buff, "%1d", i + 1);
						string fname = cex_prefix + "formula" + buff;
						sprintf(buff, "%1d", i);
						print_cex(para, fname, str_head + buff, idbdd, cextr);
          }
          clear_cex(countex, idbdd, cextr);
        }
      } 
      delete is;
      delete g;
    }
    if(options["verbosity"] > 1) {
      ftime(&tmb_formula1);
      cout << "  time for checking formula " << i+1 << " = " << ((tmb_formula1.time-tmb_formula.time) + (tmb_formula1.millitm-tmb_formula.millitm)/1000.0) << endl;
    }     
  }

  if (options["quiet"] == 0 && options["uniform"] == 0)
    cout << "done, " << is_formulae->size() << " formulae successfully read and checked" << endl;

  if(options["verbosity"] > 1) {
    ftime(&tmb_mc1);
    cout << "time for model checking = " << ((tmb_mc1.time-tmb_mc.time) + (tmb_mc1.millitm-tmb_mc.millitm)/1000.0) << endl;
  }

  delete init;
  if(!is_fairness->empty())
    fair_reach = para->bddmgr->bddZero();


   // c_end = clock();

//cout<<"the execution time for the complexity algorithm is "<< c_end - c_start<<endl;
}



