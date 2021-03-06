#ifndef CMPARCH2_CACHE_H
#define CMPARCH2_CACHE_H

#include <iostream>
#include <cmath>
#include <string>
#include <list>
#include <vector>
#include <array>
#include <map>
#include <cassert>

#define NO_WRITE_ALLOC 0
#define WRITE_ALLOC 1
#define VALID 1
#define INVALID 0
#define DIRTY 1
#define CLEAN 0
#define BAD_ADDR 0x7FFFFFFF

using std::string;
using std::array;
using std::vector;
using std::map;

typedef unsigned long int Addr;

// ----------------------- Helping & Calculation functions -------------------------- //
Addr calcOffsetMask(unsigned blockSize){
    //the mask will have 1's for bitwise and with the address to get only the offset bits
    Addr mask = 0;
    for(int i = 0 ; i < log2(blockSize) ; i++){
        mask += (Addr)pow(2,i);
    }
    return mask;
}

Addr calcSetMask(unsigned wayLength, unsigned blockSize){
    //the mask will have 1's for bitwise and with the address to get only the set bits
    Addr mask = 0;
    for(int i = (int )log2(blockSize) ; i < (log2(blockSize) + log2(wayLength)); i++){
        mask += (Addr)pow(2,i);
    }
    return mask;
}

// ===================================== Classes =================================== //

class Line{
public:
    Addr address,tag;
    bool valid;
    bool dirty;
    int LruIndicator;

    //default c'tor for cache init.
    explicit Line(bool valid=INVALID,bool dirty= CLEAN,int  priority=0):
            address(BAD_ADDR),tag(BAD_ADDR),valid(valid),dirty(dirty),LruIndicator(priority){}
    //default for insertion, and replacement.
    Line(Addr a,Addr t,int LruCount):address(a),tag(t),LruIndicator(LruCount),valid(VALID),dirty(CLEAN){}
    ~Line() = default;
};

class Cache {
public:
    vector<vector<Line>> ways;
    int misses,hits;
    Addr setMask,offsetMask;
    unsigned BlockSize;
    //values are not powered by 2
    Cache(unsigned BSize, unsigned LSize,unsigned LAssoc) : BlockSize(BSize),misses(0),hits(0)
    {
        this->offsetMask = calcOffsetMask((unsigned )pow(2,BSize));
        unsigned way_len = ((unsigned )pow(2,LSize)/(unsigned )(pow(2,BSize)*pow(2,LAssoc)));
        this->setMask = calcSetMask(way_len,(unsigned )pow(2,BSize));
        this->ways = vector<vector<Line>>(pow(2,LAssoc),vector<Line>(way_len));
    }
    ~Cache() = default;
    int lookup(Addr addr){
        Addr set = addr & setMask;
        set >>= BlockSize;
        Addr tagToSearch = addr & ~offsetMask;
        tagToSearch &= ~setMask;
        for(int i=0 ; i < ways.size() ; i++){
            if(!ways[i][set].valid || ways[i][set].address == BAD_ADDR) continue;
            if(ways[i][set].tag == tagToSearch){
                return i;
            }
        }
        return -1;
    }
    void updateLRU(Addr num,int LruCount,int index,char operation){
        Addr set=(num & this->setMask) >> BlockSize;
        ways[index][set].LruIndicator=LruCount;
        //if we are writing, mark dirty.
        ways[index][set].dirty = (operation == 'w');
    }
    int findAwayToInsert(Addr num,Addr set,Addr tag,const int* LruCount,char operation){
        int i=0,min,minIndex=0;
        min=ways[0][set].LruIndicator;
        for(i=0;i<ways.size();i++){ // find a way to insert the block to it (LRU)
            if(!(ways[i])[set].valid){
                (ways[i])[set]=Line(num,tag,*LruCount);
                if(operation=='w'){
                    (ways[i])[set].dirty=DIRTY; //we have to write it back to L2 before replacing
                }
                return -1;
            }
            if((ways[i])[set].LruIndicator < min){
                min=(ways[i])[set].LruIndicator;
                minIndex=i;
            }
        }
        return minIndex;
    }
    void l2tol1(Addr num,Cache& L2,int *LruCount, char operation){
        Addr set=(num & setMask) >> BlockSize;
        Addr tag=(num & ~offsetMask) & (~setMask);
        int minIndex = findAwayToInsert(num,set,tag,LruCount,operation);
        if(minIndex == -1) {
            //the line is inserted
            return;
        }
        if(ways[minIndex][set].dirty){//if dirty, write back to L2
            Addr set2=(ways[minIndex][set].address & L2.setMask) >> L2.BlockSize;
            Addr tag2=(ways[minIndex][set].address & ~L2.offsetMask) & (~L2.setMask);
            for(int i=0;i<L2.ways.size();i++){
                if(L2.ways[i][set2].valid && L2.ways[i][set2].tag==tag2){
                    (*LruCount) = (*LruCount) + 1;
                    L2.ways[i][set2].LruIndicator=(*LruCount);
                    L2.ways[i][set2].dirty= DIRTY;
                    break;
                }
            }
        }
        ways[minIndex][set]=Line(num,tag,(*LruCount));
        if(operation=='w'){
            ways[minIndex][set].dirty=DIRTY;
        }
    }
    void snoopL1(Cache& L1,const int minIndex,const int set){
        Addr set1=(ways[minIndex][set].address & L1.setMask) >> L1.BlockSize;
        Addr tag1=(ways[minIndex][set].address & ~L1.offsetMask) & (~L1.setMask);
        for(int i=0;i<L1.ways.size();i++){
            if(L1.ways[i][set1].valid && L1.ways[i][set1].tag==tag1){
                L1.ways[i][set1].valid=INVALID;
                break;
            }
        }
    }
    void memToL2(Addr num,Cache& L1,const int* LruCount,char operation){
        Addr set=(num & setMask)>> BlockSize;
        Addr tag=(num & ~offsetMask) & (~setMask);
        int minIndex = findAwayToInsert(num,set,tag,LruCount,operation);
        if(minIndex == -1){
            //line already inserted
            return;
        }
        // snoop L1
        snoopL1(L1,minIndex,set);
        ways[minIndex][set]=Line(num,tag,*LruCount);
        if(operation=='w'){
            ways[minIndex][set].dirty=DIRTY;
        }
    }
};

class Hierarchy {
    Cache L1,L2;
    int LRU_counter;
    unsigned access_num, cycles_num, L1Cyc, L2Cyc, MemCyc;
    unsigned WrAlloc;
public:
    Hierarchy(unsigned MemCyc, unsigned BSize, unsigned L1Size, unsigned L2Size, unsigned L1Assoc,
              unsigned L2Assoc, unsigned L1Cyc, unsigned L2Cyc, unsigned WrAlloc) :
              L1(BSize,L1Size,L1Assoc),L2(BSize,L2Size,L2Assoc),LRU_counter(0),access_num(0),cycles_num(0),L1Cyc(L1Cyc)
              ,L2Cyc(L2Cyc),MemCyc(MemCyc),WrAlloc(WrAlloc) {}

    ~Hierarchy() = default;
    void exec(Addr addr, char op){
        assert(op=='w' || op=='r');
        //new access to sim.
        this->access_num++;
        //search in L1
        int searchResWay = L1.lookup(addr);
        if(searchResWay == -1) {
            //L1 missed :(
            L1.misses++;
            //search in L2 .
            searchResWay = L2.lookup(addr);
            if(searchResWay != -1){
                //L2 hits :D
                L2.hits++;
                L2.updateLRU(addr,LRU_counter,searchResWay,op);
                if(op=='r' || WrAlloc==WRITE_ALLOC){
                    //we need to bring it to L1
                    L1.l2tol1(addr,L2,&LRU_counter,op);
                }
                cycles_num += (L2Cyc + L1Cyc);
                LRU_counter++;
                return;

            } else {
                //fuck :')
                L2.misses++;
                this->cycles_num += (L1Cyc + L2Cyc + MemCyc);
                if(op=='w' && WrAlloc==NO_WRITE_ALLOC){
                    //another access to count
                    LRU_counter++;
                    return;
                }
                L2.memToL2(addr,L1,&LRU_counter,op);
                L1.l2tol1(addr,L2,&LRU_counter,op);
                LRU_counter++;
                return;
            }
        } else {
            //L1 hits ! Let's pray we always get here.
            L1.hits++;
            L1.updateLRU(addr,LRU_counter,searchResWay,op);
            cycles_num += L1Cyc;
            LRU_counter++;
            return;
        }
    }
    double l1MissRate() const {
        return (double )L1.misses/(L1.misses + L1.hits);
    }
    double l2MissRate() const {
        return (double )L2.misses/(L2.misses + L2.hits);
    }
    double avgTime() const {
        return (double )cycles_num/access_num;
    }
};


#endif //CMPARCH2_CACHE_H
