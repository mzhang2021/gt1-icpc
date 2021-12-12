#include <bits/stdc++.h>
using namespace std;
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace __gnu_pbds;
template<class T, class U, class Compare = less<>> using order_statistic_map = tree<T, U, Compare, rb_tree_tag, tree_order_statistics_node_update>;
template<class T, class Compare = less<>> using order_statistic_set = order_statistic_map<T, null_type, Compare>;

// Adjacency_Type: array<int, X> or map<Char_Type, int> where X is the size of the alphabet
template<class Char_Type, class Adjacency_Type>
struct suffix_tree{
	int n = 0; // length of the underlying string
	vector<Char_Type> s; // underlying string
	// Begin States
	// The position of the label of the parent edge in the string, temporary length of the parent edge, suffix link, parent vertex
	vector<int> pos{0}, len{numeric_limits<int>::max()}, link{0}, pv{0};
	vector<Adjacency_Type> next{{}};
	// End States
	int new_state(int p, int l = numeric_limits<int>::max()){
		pos.push_back(p);
		len.push_back(l);
		link.push_back(-1);
		pv.push_back(-1);
		next.push_back({});
		return (int)pos.size() - 1;
	}
	int u_last = 0, extra = 0;
	void extend(Char_Type c){
		s.push_back(c), ++ n, ++ extra;
		for(auto last = 0; extra; ){
			while(extra > len[next[u_last][s[n - extra]]]) u_last = next[u_last][s[n - extra]], extra -= len[u_last];
			Char_Type edge = s[n - extra];
			int u = next[u_last][edge];
			Char_Type t = s[pos[u] + extra - 1];
			if(!u){
				u = new_state(n - extra);
				link[last] = u_last;
				last = 0;
			}
			else if(t == c){
				link[last] = u_last;
				return;
			}
			else{
				int v = new_state(pos[u], extra - 1);
				next[v][c] = new_state(n - 1), pv[next[v][c]] = v;
				next[v][t] = u, pv[u] = v;
				pos[u] += extra - 1, len[u] -= extra - 1;
				u = last = link[last] = v;
			}
			next[u_last][edge] = u, pv[u] = u_last;
			if(u_last) u_last = link[u_last];
			else -- extra;
		}
	}
	void extend(const vector<Char_Type> &s){
		for(auto c: s) extend(c);
	}
	int size() const{ // # of states
		return (int)pos.size();
	}
	int length(int u) const{ // actual length of the parent edge
		return u ? min(len[u], (int)s.size() - pos[u]) : 0;
	}
};

template<class F>
struct y_combinator_result{
	F f;
	template<class T> explicit y_combinator_result(T &&f): f(forward<T>(f)){ }
	template<class ...Args> decltype(auto) operator()(Args &&...args){ return f(ref(*this), forward<Args>(args)...); }
};
template<class F>
decltype(auto) y_combinator(F &&f){
	return y_combinator_result<decay_t<F>>(forward<F>(f));
}

template<class T>
struct fenwick_tree{
	int n;
	vector<T> data;
	fenwick_tree(){ }
	// O(n)
	fenwick_tree(int n): n(n), data(n){ }
	// O(n)
	fenwick_tree(int n, T init): fenwick_tree(vector<T>(n, init)){ }
	// O(n)
	fenwick_tree(const vector<T> &v): n((int)v.size()), data(v){
		for(auto i = 1; i <= n; ++ i) if(i + (i & -i) <= n) data[i + (i & -i) - 1] += data[i - 1];
	}
	fenwick_tree(const fenwick_tree &otr): n(otr.n), data(otr.data){
	}
	// O(log n)
	void update(int p, T x){
		assert(0 <= p && p < n);
		for(++ p; p <= n; p += p & -p) data[p - 1] += x;
	}
	// O(log n)
	T query(int r) const{
		T s{};
		for(; r > 0; r -= r & -r) s += data[r - 1];
		return s;
	}
	// O(log n)
	T query(int l, int r) const{
		assert(0 <= l && l <= r && r <= n);
		return query(r) - query(l);
	}
	// f(sum[0, r)) is T, T, ..., T, F, F, ..., F, returns min r with F (n + 1 if no such r)
	// O(log n)
	int max_pref(auto f) const{
		if(!f({})) return 0;
		int p = 0;
		T pref{};
		for(auto pw = 1 << __lg(n + 1); pw; pw >>= 1) if(p + pw <= n && f(pref + data[p + pw - 1])){
			pref += data[p + pw - 1];
			p += pw;
		}
		return p + 1;
	}
	int lower_bound(T x) const{
		if(x <= T{}) return 0;
		int p = 0;
		T pref{};
		for(auto pw = 1 << __lg(n + 1); pw; pw >>= 1) if(p + pw <= n && pref + data[p + pw - 1] < x){
			pref += data[p + pw - 1];
			p += pw;
		}
		return p + 1;
	}
	int upper_bound(T x) const{
		if(x < T{}) return 0;
		int p = 0;
		T pref{};
		for(auto pw = 1 << __lg(n + 1); pw; pw >>= 1) if(p + pw <= n && pref + data[p + pw - 1] <= x){
			pref += data[p + pw - 1];
			p += pw;
		}
		return p + 1;
	}
};

// efficient multiset when only dealing with small integers in [offset, offset + len)
// Requires fenwick_tree
template<class T>
struct integral_multiset{
	int sz = 0;
	T offset, maxval;
	vector<int> freq;
	fenwick_tree<int> data;
	integral_multiset(int len, T offset = {}): offset(offset), maxval(offset + len), freq(len), data(len){ }
	integral_multiset(const vector<T> &init, int len, T offset = 0): offset(offset), maxval(offset + len), freq(len){
		for(auto x: init){
			assert(offset <= x && x < maxval);
			++ freq[x - offset], ++ sz;
		}
		data = {freq};
	}
	integral_multiset(const integral_multiset &otr): sz(otr.sz), offset(otr.offset), maxval(otr.maxval), freq(otr.freq), data(otr.data){
	}
	friend ostream &operator<<(ostream &out, integral_multiset ms){
		out << "{";
		for(auto x = ms.offset; x < ms.maxval; ++ x) for(auto rep = 0; rep < ms.freq[x]; ++ rep) out << x << ", ";
		return ms.empty() ? out << "}" : out << "\b\b}";
	}
	int size() const{ // O(1)
		return sz;
	}
	bool empty() const{
		return !sz;
	}
	int count(T x) const{ // O(1)
		assert(offset <= x && x < maxval);
		return freq[x - offset];
	}
	void insert(T x){ // O(log len)
		assert(offset <= x && x < maxval);
		data.update(x - offset, 1), ++ freq[x - offset], ++ sz;
	}
	bool erase(T x){ // O(log len) if true, O(1) otherwise
		assert(offset <= x && x < maxval);
		return freq[x - offset] ? (data.update(x - offset, -1), -- freq[x], -- sz, true) : false;
	}
	T find_by_order(int k) const{ // O(log len)
		assert(k < sz);
		return data.max_pref([k](int pref){ return pref <= k; }) - 1 + offset;
	}
	int order_of_key(T x) const{ // O(log len)
		assert(offset <= x && x < maxval);
		return data.query(x - offset);
	}
	T front() const{ // O(log len)
		assert(sz);
		return find_by_order(0) + offset;
	}
	T back() const{ // O(log len)
		assert(sz);
		return find_by_order(sz - 1) + offset;
	}
	int lower_bound(T x) const{ // O(log len), returns maxval if no such element
		assert(offset <= x && x < maxval);
		int k = data.query(x - offset) + 1;
		return data.max_pref([k](int pref){ return pref <= k; }) - 1 + offset;
	}
	int upper_bound(T x) const{ // O(log len), returns maxval if no such element
		assert(offset <= x && x < maxval);
		int k = data.query(x - offset + 1) + 1;
		return data.max_pref([k](int pref){ return pref <= k; }) - 1 + offset;
	}
};

int main(){
	cin.tie(0)->sync_with_stdio(0);
	cin.exceptions(ios::badbit | ios::failbit);
	int n;
	vector<int> s;
	{
		string t;
		cin >> t;
		n = (int)t.size();
		for(auto c: t){
			s.push_back(c - 'a');
		}
	}
	const int mx = 26;
	suffix_tree<int, array<int, mx>> st;
	st.extend(s);
	vector<int> dfs_pos((int)st.size()), length((int)st.size());
	vector<int> dfs_order;
	{
		y_combinator([&](auto self, int u)->void{
			dfs_pos[u] = (int)dfs_order.size();
			dfs_order.push_back(u);
			for(auto c = 0; c < mx; ++ c){
				if(auto v = st.next[u][c]){
					length[v] = length[u] + st.length(v);
					self(v);
				}
			}
		})(0);
	}
	int qn;
	cin >> qn;
	vector<pair<long long, int>> q(qn);
	for(auto qi = 0; qi < qn; ++ qi){
		cin >> q[qi].first, q[qi].second = qi;
	}
	sort(q.rbegin(), q.rend());
	priority_queue<array<int, 2>, vector<array<int, 2>>, greater<>> pq;
	pq.push({0, 0});
	integral_multiset<int> ms((int)st.size());
	ms.insert(0);
	vector<array<int, 2>> res(qn, {-2, -1});
	long long cnt = 0;
	for(auto len = 0; len <= n; ++ len){
		cnt += (int)pq.size();
		while(!q.empty() && q.back().first < cnt){
			int u = dfs_order[ms.find_by_order(q.back().first - (cnt - (int)ms.size()))];
			int r = st.pos[u] + st.length(u) - (length[u] - len);
			int l = r - len;
			res[q.back().second] = {l, r};
			q.pop_back();
		}
		while(!pq.empty() && pq.top()[0] == len){
			auto [ulen, u] = pq.top();
			pq.pop();
			ms.erase(dfs_pos[u]);
			for(auto c = 0; c < mx; ++ c){
				if(auto v = st.next[u][c]){
					pq.push({ulen + st.length(v), v});
					ms.insert(dfs_pos[v]);
				}
			}
		}
	}
	for(auto [l, r]: res){
		cout << l + 1 << " " << r << "\n";
	}
	return 0;
}

/*

*/

////////////////////////////////////////////////////////////////////////////////////////
//                                                                                    //
//                                   Coded by Aeren                                   //
//                                                                                    //
////////////////////////////////////////////////////////////////////////////////////////