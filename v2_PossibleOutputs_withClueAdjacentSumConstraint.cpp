#include<iostream>
#include<iterator>
#include<algorithm>
#include<bits/stdc++.h>

using namespace std;

// #ifndef ONLINE_JUDGE
// #include "local_dbg.cpp"
// #else
// #define debug(...) 101;
// #endif
typedef  long long  int ll;
typedef  long double ld;
typedef std::vector<int> vi;
typedef std::vector<ll> vll;
typedef std::vector<ld> vld;
typedef std::vector<std::vector<ll> > vvll;
typedef std::vector<std::vector<ld> > vvld;
typedef std::vector<std::vector<std::vector<ll> > > vvvll;
typedef std::vector<string> vstr;
typedef std::vector<std::pair<ll,ll> > vpll;
typedef std::pair<ll,ll> pll;

// #include <ext/pb_ds/assoc_container.hpp>
// #include <ext/pb_ds/tree_policy.hpp>
using namespace std;
// using namespace __gnu_pbds;
// #define ordered_set     tree<ll, null_type,less<ll>, rb_tree_tag,tree_order_statistics_node_update>

#define fast            ios_base::sync_with_stdio(0); cin.tie(0); cout.tie(0)
#define pb              push_back
#define nl              "\n" 
#define all(c)          (c).begin(),(c).end()
#define iotam1          cout<<-1<<nl
#define cty             cout<<"YES"<<nl
#define ctn             cout<<"NO"<<nl
#define lmax            LLONG_MAX
#define lmin            LLONG_MIN
#define sz(v)           (v).size()
#define deci(n)         fixed<<setprecision(n)
#define c(x)            cout<<(x)
#define csp(x)          cout<<(x)<<" "
#define c1(x)           cout<<(x)<<nl
#define c2(x,y)         cout<<(x)<<" "<<(y)<<nl
#define c3(x,y,z)       cout<<(x)<<" "<<(y)<<" "<<(z)<<nl
#define c4(a,b,c,d)     cout<<(a)<<" "<<(b)<<" "<<(c)<<" "<<(d)<<nl
#define c5(a,b,c,d,e)   cout<<(a)<<" "<<(b)<<" "<<(c)<<" "<<(d)<<" "<<(e)<<nl
#define c6(a,b,c,d,e,f) cout<<(a)<<" "<<(b)<<" "<<(c)<<" "<<(d)<<" "<<(e)<<" "<<(f)<<nl

#define f(i_itr,a,n) for(ll i_itr=a; i_itr<n; i_itr++)
#define rev_f(i_itr,n,a) for(ll i_itr=n; i_itr>a; i_itr--)
#define arri(n, arr) for(ll i_itr=0; i_itr<n; i_itr++) cin>>arr[i_itr]
#define a_arri(n, m, arr) for(ll i_itr=0; i_itr<n; i_itr++) for (ll j_itr=0; j_itr<m; j_itr++) cin>>arr[i_itr][j_itr]
#define pb push_back
#define fi first
#define se second
#define print(vec,a,b) for(ll i_itr=a;i_itr<b;i_itr++) cout<<vec[i_itr]<<" ";cout<<"\n";
#define input(vec,a,b) for(ll i_itr = a;i_itr<b;i_itr++) cin>>vec[i_itr];
#define ms(a,val) memset(a,val,sizeof(a))


const ll mod = 1000000007;
const long double pi=3.14159265358979323846264338327950288419716939937510582097494459230;

ll pct(ll x) { return __builtin_popcountll(x); } // #of set bits
ll poww(ll a, ll b) { ll res=1; while(b) { if(b&1) res=(res*a); a=(a*a); b>>=1; } return res; }
ll modI(ll a, ll m=mod) { ll m0=m,y=0,x=1;  if(m==1) return 0;  while(a>1)  { ll q=a/m; ll t=m;  m=a%m;  a=t; t=y; y=x-q*y;  x=t; } if(x<0) x+=m0; return x;}
ll powm(ll a, ll b,ll m=mod) {ll res=1; while(b) { if(b&1) res=(res*a)%m; a=(a*a)%m; b>>=1; } return res;}

void ipgraph(ll,ll);
void ipgraph(ll); ///for tree
void dfs(ll node,ll par);

//******************************************************************************************************************************************* /

const ll N=2e5+5;
// ll inp[N];
// vll adj[N];      ///for graph(or tree) use this !!-><-!!
ll matrix[9][9] = {{0,18,0,0,0,0,7,0,0},{0,0,0,0,12,0,0,0,0},{0,0,9,0,0,0,0,31,0},{0,0,0,0,0,0,0,0,0},{0,5,0,11,0,22,0,22,0},{0,0,0,0,0,0,0,0,0},{0,9,0,0,0,0,19,0,0},{0,0,0,0,14,0,0,0,0},{0,0,22,0,0,0,0,15,0}};
bool avai[9][9];

vpll already;
vvll clueSet;
vll totNeighs;

ll dirx[4]={0,0,-1,1};
ll diry[4]={1,-1,0,0};

ll dirano[4] = {1,-1,1,-1};
ll dirano2[4] = {1,1,-1,-1};

vpll hooks;
ll number=0;

vll clueNeighbour[9][9];

vll permutation = {1,2,3,4,5,6,7,8,9};

// vll permutation = {1,2,3,4,8,7,5,9,6};

bool ispossible(ll clueno){
    ll ssum=0;
    f(i,0,1ll<<totNeighs[clueno]){
        ssum=0;
        f(j,0,totNeighs[clueno])
            if((i>>j)&1ll) ssum+= clueSet[clueno][j];
        if(ssum==matrix[already[clueno].first][already[clueno].second]) return 1;
    }

    return 0;
}

ll dcounter=0;

void recur(ll stx,ll sty,ll enx,ll eny)
{
    ll llen=enx-stx+1;

    if(llen==1)
    {
        number++;
        if(!(number%10000)) c1(number);

        if(!avai[stx][sty]) return;

        // matrix[stx][sty]=llen;  //change here
        matrix[stx][sty]=permutation[llen-1];
        bool isgood=1;

        for(ll neighs : clueNeighbour[stx][sty])
        {
            clueSet[neighs].push_back(matrix[stx][sty]);
            if(isgood && clueSet[neighs].size()==totNeighs[neighs])
            {
                if(!(ispossible(neighs))) isgood=0;
            }
        }

        if(isgood)
        {
            c1("found !!!");
            for(pll hk:hooks)
                csp(hk.first),csp(hk.second),csp(",");
            c1("");

            f(i,0,9){
                f(j,0,9){
                    cout << setw(3) << (matrix[i][j]);
                }
                c1("");
            }
        }

        matrix[stx][sty]=0;
        // bool isgood=1;

        for(ll neighs : clueNeighbour[stx][sty])
        {
            clueSet[neighs].pop_back();
        }
        
        return;
    }

    ll cornerx=stx,cornery=sty;

    f(hook,0,4)
    {
        bool isgood=1;
        f(j,0,llen){
            if(avai[cornerx][cornery+dirano[hook]*j]){
                // matrix[cornerx][cornery+dirano[hook]*j]=llen;   //change here
                matrix[cornerx][cornery+dirano[hook]*j]=permutation[llen-1];
                for(ll neighs : clueNeighbour[cornerx][cornery+dirano[hook]*j])
                {
                    clueSet[neighs].push_back(matrix[cornerx][cornery+dirano[hook]*j]);
                    if(isgood && clueSet[neighs].size()==totNeighs[neighs])
                    {
                        if(!(ispossible(neighs))) isgood=0;
                    }
                }
            }

            if(j && avai[cornerx+dirano2[hook]*j][cornery]) {
                // matrix[cornerx+dirano2[hook]*j][cornery]=llen;  //change here
                matrix[cornerx+dirano2[hook]*j][cornery]=permutation[llen-1];

                for(ll neighs : clueNeighbour[cornerx+dirano2[hook]*j][cornery])
                {
                    clueSet[neighs].push_back( matrix[cornerx+dirano2[hook]*j][cornery]);
                    if(isgood && clueSet[neighs].size()==totNeighs[neighs])
                    {
                        if(!(ispossible(neighs))) isgood=0;
                    }
                }

            }
        }
        // 1 1 0 0
        // 1 0 0 -1
        // 0 1 -1 0
        // 0 0 -1 -1
        hooks.push_back({cornerx,cornery});
        if(isgood)
            recur(stx+(hook<2ll),sty+((hook&1ll) == 0),enx-(hook>1ll),eny - (hook&1ll));
        else
        {
            dcounter++;
            ///Just for verification, Verified!!!

            // c1(dcounter);
            // if(dcounter>=160)
            // {
            //     f(i,0,9){
            //         f(j,0,9){
            //             cout << setw(3) << (matrix[i][j]);
            //         }
            //         c1("");
            //     }
            // } 
        }
        hooks.pop_back();

        f(j,0,llen){
            if(avai[cornerx][cornery+dirano[hook]*j]){
                matrix[cornerx][cornery+dirano[hook]*j]=0;
                for(ll neighs : clueNeighbour[cornerx][cornery+dirano[hook]*j])
                {
                    clueSet[neighs].pop_back();
                }
            }

            if(j && avai[cornerx+dirano2[hook]*j][cornery]) {
                matrix[cornerx+dirano2[hook]*j][cornery]=0;
                for(ll neighs : clueNeighbour[cornerx+dirano2[hook]*j][cornery])
                {
                    clueSet[neighs].pop_back();
                }

            }
        }
        
        if(hook==0)
            cornery=eny;
        else if(hook==1)
            cornerx=enx,cornery=sty;
        else if(hook==2)
            cornery=eny;
    }

}

void ok_boss()
{
    recur(0,0,8,8);

    return;
}

int main()
{
    #ifndef ONLINE_JUDGE
        freopen("input.txt", "r", stdin);
        freopen("output.txt", "w", stdout);
        freopen("error.txt", "w", stderr);
    #endif

    fast;

    /// std::cout << fixed<<setprecision(15); ///activate it if the answers are in decimal.

    auto start = std::chrono::high_resolution_clock::now();

    ll qq_itr = 1;

    f(i,0,9){
        f(j,0,9){
            if(matrix[i][j]==0) avai[i][j]=1;
            else
            {
                avai[i][j]=0,already.push_back(pll({i,j}));
                clueSet.push_back({});
                totNeighs.pb(4);

                ll newx,newy;

                f(dir,0,4)
                {
                    newx = i + dirx[dir];
                    newy = j + diry[dir];

                    if(newx>=0 && newy>=0 && newx<9 && newy<9)
                        clueNeighbour[newx][newy].push_back(already.size()-1);
                    else
                        totNeighs.back()--;
                }
            }
        }
        // c1("");
    }

    f(i,0,9){
        f(j,0,9){
            cout << setw(3) << (matrix[i][j]);
        }
        c1("");
    }

    c1("");

    // cin >> qq_itr;


    do{
        // debug(qq_itr);
        // debug(permutation);
        qq_itr++;
        // if(qq_itr==1000) break;

        f(i,0,9)
            if(permutation[i]>((i<<1ll)+1)) continue;

        ok_boss();

    }while(next_permutation(permutation.begin(),permutation.end()));

    auto end = std::chrono::high_resolution_clock::now();

    std::chrono::duration<double> duration = end - start;

    std::cout << "Time taken: " << duration.count() << " seconds" << std::endl;

    return 0;
}


/*
void ipgraph(ll nodes_ipg,ll edgs_ipg)
{
    f(i,0,nodes_ipg)
        adj[i].clear();

    ll fir,sec;
    while(edgs_ipg--)
    {
        cin>>fir>>sec;
        fir--,sec--;        ///turn it off if it is 0-indexed
        adj[fir].pb(sec);
        adj[sec].pb(fir);       ///remove this if directed !!!
    }
    return;
}

void ipgraph(ll nodes_ipg)
{
    ipgraph(nodes_ipg,nodes_ipg-1);
}


void dfs(ll node,ll par=-1)
{
    for(ll chd : adj[node])
    {
        if(chd==par)
            continue;

        dfs(chd,node);
    }

    return;
}
*/
