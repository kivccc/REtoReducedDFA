#include <iostream>
#include <stack>
#include <string>
#include <vector>
#include <algorithm>
#include <set>
using namespace std;

set<char> TerminalSet;      //터미널 셋 저장

struct State {
    int stateID;
    string StateName;           //q000,q001..q200

    vector<pair<char, int>> transitions;            // (terminal , 출력상태)
    vector<State*> epsilonTransitions;              //e - closure를 위해 전이함수중 e전이만 state포인터 저장
    int flag = 0;               // 1이면 start state, 2이면 final state, 0이면 아무것도아님
    State(int id) {
        stateID = id;
        StateName = "q" + to_string(stateID);
    }
};

struct DFAState {
    int DFAstateID;
    string DFAStateName;           //q000,q001..q200

    //vector<pair<char, int>> DFAtransitions;
    vector<pair<char, DFAState*>> DFAtransitions;

    //vector<State*> states_combined;         //입실론클로져시 "NFA state 묶어서" 새로운 상태로 전환
    set<State*> states_combined;         //입실론클로져시 "NFA state 묶어서" 새로운 상태로 전환
     
    int flag = 0;               // 1이면 start state, 2이면 final state, 0이면 아무것도아님
    int start_flag = 0;
    int final_flag = 0;
    DFAState(int id)
    {
        DFAstateID = id;
        DFAStateName = "Q" + to_string(DFAstateID);
    }
};
vector<DFAState*>tmp_dfa_set; //loop 중복 검사용 vector
vector<DFAState*>DFAResult;   //DFA 변환 결과 vector

void findEpsilonTransitions(vector<State*> nfaStates,State* state)          //각 상태에서 입실론전이를 찾아서 벡터에삽입
{
    for (auto transition : state->transitions)              //전달받은인수 state에서 loop
    {
        if (transition.first == 'E')                        //state의 transition가 입실론이면
        {
            for (auto state_for_loop : nfaStates)                    //모든 스테이트 loop해서 전이결과 상태를 찾고 원본 state의 입실론 전이 벡터삽입
            {
                if (state_for_loop->stateID == transition.second)
                    state->epsilonTransitions.push_back(state_for_loop);
            }
        }
    }
}

set<State*> epsilonClosure(State* state)        //epsilon 중복 방지 위해 set
{
    set<State*> closure;                    //e-closure된 state집합
    stack<State*> stck;
    stck.push(state);           
    closure.insert(state);                  //e-closure 초기 상태 삽입

    while (!stck.empty()) 
    {
        State* currentState = stck.top();
        stck.pop();

        for (State* nextState : currentState->epsilonTransitions) //loop 돌아서 nextstate의 e-trans된 상태들을 closure에 삽입
        {
            if (closure.find(nextState) == closure.end())  //find결과가 없으면 end()반환 = e-trans된 nextstate가 클로져없다면 삽입
            {
                closure.insert(nextState);
                stck.push(nextState);                       //입실론전이된상태에서 또 다시 입실론 전이 체크를 위해 stck에 push , 다시 stck이 빌때까지 closure에 추가하는 과정 loop
            }                                 
        }
    }
    return closure;
}

void ConvertDFA(vector<DFAState*>dfaset, DFAState* dfastate, vector<State*> nfaStates, int& StateCount)    //DFAState* dfastate -> 다시 e클로저해서 추가할 벡터 vector<State*> nfaStates -> 원본 enfa벡터
{
    for (auto terminal : TerminalSet)                   //각 터미널에 대한 delta function찾기 ex 1,3,4에 대해서  a b c terminal 전이 확인
    {
        set<State*>state_after_trans;
        for (auto state : dfastate->states_combined)    //dfa state의 모든 state에 대해 loop ex 1,3,4
        {
            for (auto transition : state->transitions)              //각 state의 transition체크   ex a 터미널에 대해1의 전이확인,2의전이확인,3의전이확인
            {
                if (transition.first == terminal)                        //state의 transition의 터미널이 체크하는 터미널과 동일하면(전이가 존재하면)
                {                                                       //묶어서 다시 최종적으로 다시 e-closure 진행      ex a의 경우 2가 state_after_trans에 저장 ,  c의 경우 3,4가 저장
                    for (auto tmp_state : nfaStates)
                    {
                        if (transition.second == tmp_state->stateID)
                            state_after_trans.insert(tmp_state);
                    }

                }
            }
        }
        if (!state_after_trans.empty()) //다시 e-closure할게 존재한다면  ex (134) -> "a" -> 2 - > e(2) - > 2가 저장     
        {
            set<State*>states_after_e_closure;
            set<State*>tmp_set;
            for (auto tmpstate : state_after_trans)
            {
                tmp_set = epsilonClosure(tmpstate);
                states_after_e_closure.insert(tmp_set.begin(), tmp_set.end());
            }
            
            int check = 0;      //기본상태는 0, 1은 자기 자신을 가리킬떄, 2는 이미 있는 dfastate을 가리킬때
            if (dfastate->states_combined == states_after_e_closure)        //동일한 state는 무한루프돌음
            {
                check = 1;
            }

            int index = 0;
            if (check != 1)
            {
                for (index = 0; index < tmp_dfa_set.size(); index++)
                {
                    if (tmp_dfa_set[index]->states_combined == states_after_e_closure)
                    {
                        check = 2;
                        break;
                    }
                }
            }

            if (check==0)
            {
                DFAState* newDfaState = new DFAState(StateCount++);       //새로운 DFA의 Start State 생성     
               
                for (auto state : states_after_e_closure)                                                  //states_after_e_closure가 비었는지 체크해야되나?
                    newDfaState->states_combined.insert(state);


                tmp_dfa_set.push_back(newDfaState);

                ConvertDFA(dfaset, newDfaState, nfaStates, StateCount);
                dfastate->DFAtransitions.emplace_back(terminal, newDfaState);

                //dfaset.push_back(newDfaState);
                DFAResult.push_back(newDfaState);
         
            }
            else if(check==1)
            {
                dfastate->DFAtransitions.emplace_back(terminal, dfastate);      //자기 자신 가리키기
            }
            else if (check == 2)
            {
                dfastate->DFAtransitions.emplace_back(terminal, tmp_dfa_set[index]);
            }
        }
    }
}

vector<DFAState*> ENFAtoDFA(vector<State*> nfaStates)
{
    vector<DFAState*>dfaset;

    State* state = nfaStates[0];
    int StateCount = 0;
   
    for (auto state_for_loop : nfaStates)
        findEpsilonTransitions(nfaStates, state_for_loop);  
    set<State*>StartSet = epsilonClosure(state);                //enfa의 startstate에 대해서 e-closure해서 나온 set을 startset에 할당 ex 1,3,4

    DFAState* dfastate = new DFAState(StateCount++);                       //새로운 DFA의 Start State 생성
    for (auto state : StartSet)
        dfastate->states_combined.insert(state);             //StartState에 기존 enfa state집합 할당        ex 1,3,4
    DFAResult.push_back(dfastate);

    ConvertDFA(dfaset, dfastate, nfaStates, StateCount);   //start만 따로 e-closure진행하고 나머지는 ConvertDFA 재귀호출
    dfaset.push_back(dfastate);

    return dfaset;
}

void printDFA(vector<DFAState*> dfaStates)          //DFA 출력함수
{
    int size_for_print = 0;
    cout << "StateSet = { ";
    for (auto state : dfaStates)                    //State Set 출력
    {
        size_for_print++;
        cout << state->DFAStateName;
        if (size_for_print != dfaStates.size())
            cout << ", ";
    }
    cout << " }\n";

    //sort(TerminalSet.begin(), TerminalSet.end());                                           //terminal set 출력
    //TerminalSet.erase(unique(TerminalSet.begin(), TerminalSet.end()), TerminalSet.end());     
    cout << "TerminalSet = { ";
    size_for_print = 0;
    for (char terminal : TerminalSet)
    {
        size_for_print++;
        cout << terminal;
        if (size_for_print != TerminalSet.size())
            cout << ", ";
    }
    cout << " }\n";

    for (auto state : dfaStates)                            //delta function 출력
    {
        cout << "State " << state->DFAStateName << ": ";

        sort(state->DFAtransitions.begin(), state->DFAtransitions.end());
        for (auto transition : state->DFAtransitions)
        {
            cout << "(" << transition.first << ", " << transition.second->DFAStateName << ") ";
        }
        cout << endl;
    }

    for (auto state : dfaStates)                            //Startstate 출력
    {
        if (state->start_flag == 1)
            cout << "StartState = " << state->DFAStateName << endl;
    }

    cout << "FinalStateSet  = { ";

    for (auto state : dfaStates)                            //Finalstateset출력
    {
        if (state->final_flag == 2)
        {

            cout << state->DFAStateName<<" ";
        }
    }
    cout << " }" << endl;
}

struct TreeNode                 //RE to Tree에 쓰이는 Node
{
    char value;
    TreeNode* left;
    TreeNode* right;

    TreeNode(char value, TreeNode* left = nullptr, TreeNode* right = nullptr)
    {
        this->value = value;
        this->left = left;
        this->right = right;
    }
};

TreeNode* createNode(char value, TreeNode* left = nullptr, TreeNode* right = nullptr) {
    TreeNode* newNode = new TreeNode(value, left, right);
    return newNode;
}

bool alphabetCheck(char c)      //알파벳 제한
{
    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'))
        return true;
    else
        return false;
}

int getPriority(char op)    //우선순위 설정
{
    if (op == '*')          //closure
        return 3;
    else if (op == '.')     //concat
        return 2;
    else if (op == '+')     //union
        return 1;
    else
        return 0;
}

void clearStartFinalFlag(vector<State*> nfaStates)
{
    for (auto state : nfaStates)
    {
        state->flag = 0;
    }
}
void clearFlag(State* state)
{
    state->flag = 0;
}
void setStartFlag(State* state)
{
    state->flag = 1;
}
void setFinalFlag(State* state)
{
    state->flag = 2;
}

vector<State*> REtoENFA(TreeNode* node, int& stateCount)        //트리로 변환된 정규표현에서 E NFA
{
    vector<State*> nfaStates;
    
    if (node == nullptr)
        return nfaStates;

    if (alphabetCheck(node->value))                 //teminal symbol일 경우 startstate,finalstate생성후 연결
    {
        State* startState = new State(stateCount++);
        State* finalState = new State(stateCount++);


        startState->flag = 1;
        finalState->flag = 2;

        startState->transitions.emplace_back(node->value, finalState->stateID);
        nfaStates.push_back(startState);
        nfaStates.push_back(finalState);
        TerminalSet.insert(node->value);
    }
    else                                            //operator 일 경우 ( * , . , + )
    {
        vector<State*> leftNFA = REtoENFA(node->left, stateCount);
        vector<State*> rightNFA = REtoENFA(node->right, stateCount);    //말단노드 접근 for dfs

        if (node->value == '*')                                         //*는 2개의 startstate,finalstate , 4개의 입실론 추가 연결
        {
            State* startState = new State(stateCount++);
            State* finalState = new State(stateCount++);      

            clearStartFinalFlag(leftNFA);     //새로운 스타트,파이널 상태할당을 위해초기화
            clearStartFinalFlag(rightNFA);     //새로운 스타트,파이널 상태할당을 위해초기화
            startState->flag = 1;
            finalState->flag = 2;

            startState->transitions.emplace_back('E', leftNFA[0]->stateID);     //start에서 바로앞 입실론연결
            startState->transitions.emplace_back('E', finalState->stateID);       //start에서 final 입실론연결


            leftNFA.back()->transitions.emplace_back('E', finalState->stateID);    //원본fianl과 확장fianl 입실론연결
            leftNFA.back()->transitions.emplace_back('E', leftNFA[0]->stateID);    //원본fianl과 원본start 입실론연결


            nfaStates.push_back(startState);
            nfaStates.insert(nfaStates.end(), leftNFA.begin(), leftNFA.end());
            nfaStates.push_back(finalState);                                        //스타트,중간,마지막 상태 순서대로 push
        }
        else if (node->value == '.')                                //.은 1개의 입실론 연결
        {
            nfaStates = leftNFA;
            
            clearFlag(leftNFA[leftNFA.size()-1]);
            clearFlag(rightNFA[0]);

            leftNFA.back()->transitions.emplace_back('E',rightNFA.front()->stateID);    //좌nfa 끝과 우nfa초기 연결

            nfaStates.insert(nfaStates.end(), rightNFA.begin(), rightNFA.end());
            
        }
        else if (node->value == '+')                                //+는 2개의 startstate,finalstate , 4개의 입실론 추가 연결
        {
            State* startState = new State(stateCount++);
            State* finalState = new State(stateCount++);

            clearStartFinalFlag(leftNFA);     //새로운 스타트,파이널 상태할당을 위해초기화
            clearStartFinalFlag(rightNFA);     //새로운 스타트,파이널 상태할당을 위해초기화
            startState->flag = 1;
            finalState->flag = 2;


            startState->transitions.emplace_back('E', leftNFA[0]->stateID); 
            startState->transitions.emplace_back('E', rightNFA[0]->stateID);        //새로운 스타트를 좌,우nfa원래 스타트와 연결



            leftNFA.back()->transitions.emplace_back('E', finalState->stateID);
            rightNFA.back()->transitions.emplace_back('E', finalState->stateID);    //좌,우nfa원래 파이널과 새로운 파이널 연결
            


            nfaStates.push_back(startState);
            nfaStates.insert(nfaStates.end(), leftNFA.begin(), leftNFA.end());
            nfaStates.insert(nfaStates.end(), rightNFA.begin(), rightNFA.end());
            nfaStates.push_back(finalState);                                        // 새로운 start, 좌,우 ,새로운final push
        }
    }




    return nfaStates;
}

void printNFA(vector<State*> nfaStates)             //NFA 출력함수
{
    int size_for_print = 0;
    cout << "StateSet = { ";
    for (auto state : nfaStates)                    //State Set 출력
    {
        size_for_print++;
        cout << state->StateName;
        if (size_for_print != nfaStates.size())
            cout << ", ";
    }
    cout << " }\n";                                 

  
    cout << "TerminalSet = { "; 
    size_for_print = 0;
    for (char terminal : TerminalSet)
    {
        size_for_print++;
        cout << terminal;
        if (size_for_print != TerminalSet.size())
            cout << ", ";
    }
    cout << " }\n";


    cout << "DeltaFunctions  = { " << endl;
    for (auto state : nfaStates)                            //delta function 출력
    {
        cout << "   State " << state->StateName << ": ";

        //sort(state->transitions.begin(), state->transitions.end());
        for (auto transition : state->transitions) 
        {
            cout << "(" << transition.first << ", " << transition.second << ") ";
        }
        cout << endl;
    }

    for (auto state : nfaStates)                            //Startstate 출력
    {
        if (state->flag == 1)
            cout << "StartState = " << state->StateName << endl;
    }

    cout << "FinalStateSet  = { ";
    for (auto state : nfaStates)                            //Finalstateset출력
    {
        if (state->flag == 2)
        {
            
            cout << state->StateName;
        }
    }
    cout << " }" << endl;
}

TreeNode* ReToTree(string regex)                    //정규 표현을 우선순위가있는 tree로 변환
{
    stack<TreeNode*> nodeStack;
    stack<char> opStack;                            //op스택에 re의 ch하나씩 check하고 push

    for (char ch : regex)                           //정규 표현 한글자씩 
    {
        if (ch == '(')
        {
            opStack.push(ch);
        }
        else if (ch == ')')
        {
            while (!opStack.empty() && opStack.top() != '(')        // 괄호 안 우선 처리를 위해 while로 loop
            {
                char op = opStack.top();
                opStack.pop();

                TreeNode* rightNode = nodeStack.top();
                nodeStack.pop();
                TreeNode* leftNode = nodeStack.top();
                nodeStack.pop();

                TreeNode* newNode = createNode(op, leftNode, rightNode);
                nodeStack.push(newNode);
            }

            if (!opStack.empty() && opStack.top() == '(')
                opStack.pop();
        }
        else if (ch == '*' || ch == '.' || ch == '+')       // closure -> * concat -> . union - > +
        {
            int currPriority = getPriority(ch);             //각 연산자의 우선순위 체크

            while (!opStack.empty() && opStack.top() != '(' && getPriority(opStack.top()) >= currPriority)  //opstack check후 우선순위 비교
            {
                char op = opStack.top();
                opStack.pop();

                TreeNode* rightNode = nullptr;
                TreeNode* leftNode = nullptr;

                if (op != '*') {
                    rightNode = nodeStack.top();
                    nodeStack.pop();
                }

                leftNode = nodeStack.top();
                nodeStack.pop();

                TreeNode* newNode = createNode(op, leftNode, rightNode);
                nodeStack.push(newNode);
            }

            opStack.push(ch);
        }
        else
        {
            if (alphabetCheck(ch))
            {
                TreeNode* newNode = createNode(ch);
                nodeStack.push(newNode);
            }
        }
    }

    while (!opStack.empty())
    {
        char op = opStack.top();
        opStack.pop();

        TreeNode* rightNode = nullptr;
        TreeNode* leftNode = nullptr;

        if (op != '*') {
            rightNode = nodeStack.top();
            nodeStack.pop();
        }

        leftNode = nodeStack.top();
        nodeStack.pop();

        TreeNode* newNode = createNode(op, leftNode, rightNode);
        nodeStack.push(newNode);
    }

    return nodeStack.top();
}

void printTree(TreeNode* node, int depth) {
    if (node != nullptr)
    {
        printTree(node->right, depth + 1);

        for (int i = 0; i < depth; i++)
            cout << "  ";
        cout << node->value << "\n";
        printTree(node->left, depth + 1);
    }
}

string addConcat(string regex)          //concat 축약표현을 다시 concat연산자 추가해서 re재구성
{
    string concat_added_regex;

    for (int i = 0; i < regex.size(); i++)
    {
        concat_added_regex += regex[i];     // terminal , * , ( , ) , . , + ,
      
        if (i+1 != regex.size())
        {
            if (alphabetCheck(regex[i]))
            {
                if (alphabetCheck(regex[i + 1]) || regex[i + 1] == '(')
                    concat_added_regex += '.';
            }
            else if (regex[i] == ')'|| regex[i] == '*')
            {
                if (alphabetCheck(regex[i + 1]))
                    concat_added_regex += '.';
            }
        }
    }
    return concat_added_regex;
}





void searchStartNFinalStateDFA(vector<DFAState*>dfaStates)
{
    for (int i = 0; i < dfaStates.size(); i++)
    {
        for (auto dfastate : dfaStates[i]->states_combined)
        {
            if (dfastate->flag == 1)           //start일경우
                dfaStates[i]->start_flag = 1;
            else if(dfastate->flag == 2)
                dfaStates[i]->final_flag = 2;
        }
    }
}


int main()
{
    string regex = "(b+aa+ac+aaa+aac)*";
    regex = addConcat(regex);
    cout << "\n"+ regex + "\n\n\n";
    TreeNode* treeRoot = ReToTree(regex);
    //printTree(treeRoot, 0);

    
    int stateCount = 0;
    vector<State*> nfaStates = REtoENFA(treeRoot, stateCount);
    cout << "--------------------   ENFA INFORMATION   --------------------" << endl;
    printNFA(nfaStates);
    

    cout << "--------------------   DFA INFORMATION   --------------------" << endl;

    ENFAtoDFA(nfaStates);                   //nfaState를 변환하고 변환한 결과물을 DFAResult에 복사한다.
    searchStartNFinalStateDFA(DFAResult);
    printDFA(DFAResult);


    return 0;
}