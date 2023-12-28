
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "sfmm.h"
#include <errno.h>

#define HSIZE sizeof(sf_header)
#define BOUND 2*(sizeof(sf_header))
#define MIN (sizeof(sf_block))
int init_state=0;
static size_t total_payload=0;
static size_t total_allocated=0;
static size_t max_aggregate=0;
static size_t create(size_t payload, size_t size, int alloc, int pre_alloc, int unused)
{
    size_t result=0;
    result|=((uint64_t)payload<<32);
    result|=(size);
    result|=(alloc<<3);
    result|=(pre_alloc<<2);
    result|=(unused);
    return result;
}
static int get_prev_alloc(sf_header header)
{
    return (header & 0x0000000000000004)>>2;
}
static void set_prev_alloc(sf_block *block)
{
    block->header=(block->header) |(1<<2);
}
static void clear_prev_alloc(sf_block* block)
{
    block->header=(block->header) & ~(1<<2);
}
static size_t get_payload(sf_header header)
{
    return (header >>32) & 0x00000000FFFFFFFF;
}
static int get_alloc(sf_header header)
{
    return (header & 0x0000000000000008)>>3;
}
static size_t b_size(sf_header h)
{
    return (h & 0x00000000FFFFFFF0);
}
static sf_block* get_next_block(sf_block* current)
{
    return (sf_block*)((char*)current + b_size(current->header));
}
static void initialize_free_lists()
{
    for(int i=0; i<NUM_FREE_LISTS; i++)
    {
        sf_free_list_heads[i].body.links.next=&sf_free_list_heads[i];
        sf_free_list_heads[i].body.links.prev=&sf_free_list_heads[i];
    }
}
static int find(size_t size)
{
    int lower=1;
    int upper=2;
    int start=0;
    if(size<=MIN)
    {
        return start;
    }
    start++;
    while(start < NUM_FREE_LISTS-2)
    {
        if(size >(lower*MIN) && size<=(upper*MIN))
        {
            return start;
        }
        int next=lower+upper;
        lower=upper;
        upper=next;
        start++;
    }
    return start;
}
static struct sf_block* search_list(size_t size)
{
    int start=find(size);
    while(start<=NUM_FREE_LISTS-2)
    {
        struct sf_block *head= &sf_free_list_heads[start];
        if((head->body.links.next)!=head && head->body.links.prev!=head)
        {
            struct sf_block *current=head->body.links.next;
            while(current!=head)
            {
                if(b_size(current->header)>=size)
                {
                    return current;
                }
                current=current->body.links.next;
            }
        }
        start++;
    }
    struct sf_block* wilderness= &sf_free_list_heads[NUM_FREE_LISTS-1];
    if(wilderness->body.links.next!=wilderness && wilderness->body.links.prev!=wilderness)
    {
        return wilderness->body.links.next;
    }
    return NULL;
}
static void insert(struct sf_block * pointer, size_t size)
{
    struct sf_block* head = &sf_free_list_heads[size];
    struct sf_block* next= sf_free_list_heads[size].body.links.next;
    struct sf_block* prev= sf_free_list_heads[size].body.links.prev;
    if(next !=head && prev!=head)
    {
        pointer->body.links.next=next;
        pointer->body.links.prev=head;
        next->body.links.prev=pointer;
        head->body.links.next=pointer;
    }  
    else if(next ==head && prev==head)
    {
        pointer->body.links.next=head;
        pointer->body.links.prev=head;
        head->body.links.next=pointer;
        head->body.links.prev=pointer;
    }
}
static void remove_block(struct sf_block* block)
{
    struct sf_block* next= block->body.links.next;
    struct sf_block* prev= block->body.links.prev;
    prev->body.links.next=next;
    next->body.links.prev=prev;
    block->body.links.next=NULL;
    block->body.links.prev=NULL;
}
static void *combine_wilderness(struct sf_block* current, struct sf_block* new)
{
    size_t prev=b_size(current->header);
    size_t next=b_size(new->header);
    size_t total_size=prev+next;
    current->header=create(0,total_size,0,0,0);
    struct sf_block* footer=(struct sf_block*)((char*)new + next);
    footer->prev_footer=current->header;
    return current;
}
static void *combine(sf_block* current)
{
    size_t prev=get_alloc(current->prev_footer);
    sf_block* next_block= get_next_block(current);
    size_t next=get_alloc(next_block->header);
    size_t current_size=b_size(current->header);
    if(prev && next)
    {
        return current;
    }
    else if (prev && !next)
    {
        current_size+=b_size(next_block->header);
        current->header=create(0,current_size,0, get_prev_alloc(current->header), 0);
        sf_block* footer=(sf_block*)((char*)current +current_size);
        footer->prev_footer=current->header;
        remove_block(next_block);
        //sf_show_block(next_block);
    }
    else if (!prev && next)
    {
        current_size+=b_size(current->prev_footer);
        sf_block* footer=(sf_block *)((char*)current+b_size(current->header));
        sf_block* previous=(sf_block*)((char*)current-b_size(current->prev_footer));
        footer->prev_footer=create(0,current_size,0, get_prev_alloc(previous->header), 0);
        previous->header=create(0,current_size,0, get_alloc(previous->prev_footer), 0);
        remove_block(previous);
        current=previous;
    }
    else{
        current_size+=b_size(next_block->header)+b_size(current->prev_footer);
        sf_block* previous=(sf_block*)((char*)current-b_size(current->prev_footer));
        previous->header=create(0,current_size,0, get_alloc(previous->prev_footer), 0);
        sf_block* next=(sf_block*)((char*)current+b_size(current->header)+b_size(next_block->header));
        next->prev_footer=previous->header;
        remove_block(previous);
        remove_block(next_block);
        current=previous;
    }
    return current;
}
void *alloc(struct sf_block* current,size_t size_needed, size_t payload)
{
    //remove block from free list and allocate
    struct sf_block* space = current;
    size_t current_size=b_size(space->header);// The size of the block assigned
    int wild=0;
    if(space->body.links.prev ==&sf_free_list_heads[NUM_FREE_LISTS-1])
    {
        wild=1;//wilderness block
    }
    if(current_size > size_needed && (current_size-size_needed)< MIN)// if the block is larger than needed, but the difference is less than MIN
    {
        size_needed=current_size;
    }
    space->header=create(payload, size_needed, 1,get_alloc(space->prev_footer),0);
    remove_block(space);
    total_allocated+=size_needed; // add the allocated size to the total 
    struct sf_block* next =(struct sf_block*) ((char*)space + size_needed);
    next->prev_footer=space->header;
    set_prev_alloc(next);//set the prev_alloc of next block
  
    //If the block is able to split
    if(current_size!=size_needed)//block not the exact size
    {
        size_t difference=current_size-size_needed;
        if(difference >= MIN)
        {
             //Store the remaining list in the appropriate list
            struct sf_block* remaining =(struct sf_block*) ((char*)space + size_needed);
            remaining->prev_footer = space->header;
            remaining->header=create(0,difference,0,get_alloc(remaining->prev_footer),0);
            struct sf_block* footer =(struct sf_block*) ((char*)remaining + difference);
            footer->prev_footer=remaining->header;
            //This block is not the wilderness block
            if(wild==0)
            {
                insert(remaining, find(difference));
            }
            else
            {
                sf_free_list_heads[NUM_FREE_LISTS-1].body.links.next=remaining;
                sf_free_list_heads[NUM_FREE_LISTS-1].body.links.prev=remaining;
                remaining->body.links.next=&sf_free_list_heads[NUM_FREE_LISTS-1];
                remaining->body.links.prev=&sf_free_list_heads[NUM_FREE_LISTS-1];
            }
            //sf_show_block(remaining);
        }
    }
    return space->body.payload;
}
void *sf_malloc(size_t size) {
    if(size==0)
    {
        return NULL;
    }
    size_t block_size=MIN;
    size_t payload=size;
    if((size + 16) > MIN)
    {
        block_size=((payload + BOUND)+BOUND-1) & ~(0xf);
    }
    total_payload+=payload;// add the payload total payload
    if(max_aggregate<total_payload)
    {
        max_aggregate=total_payload;
    }
    if(init_state==0)
    {
        initialize_free_lists(); //set up the free_lists
    }
    struct sf_block* head = (search_list(block_size)); //look for free space
    size_t size_needed=block_size;
    size_t current_size=0;
    if(head==NULL)// CASE 1: No space +  no wilderness block
    {
        head=&sf_free_list_heads[NUM_FREE_LISTS-1];//Set pointer at wilderness block
        if(init_state==0)
        {
            size_needed+=(MIN + 16);
        }
        char* current=sf_mem_grow();
        if(current==NULL)
        {
            sf_errno=ENOMEM;
            return NULL;
        }
        current_size+=PAGE_SZ;
        struct sf_block* start=(struct sf_block*)(current);//points to the start of the wilderness block
        if(init_state==0)// not initialized
        {
            start->header=create(0,MIN,1,0,0);//Set prolouge
            struct sf_block* next=(struct sf_block*)((char*)current + MIN);
            next->prev_footer=start->header;//Set footer of prologue
            next->header=create(0,current_size-MIN-16,0,1,0);
            start=next;
            init_state=1;
        }
        else
        {
            start=(struct sf_block*)(current-2*HSIZE);//points to the footer of wild block
            start->header=create(0,current_size,0,get_alloc(start->prev_footer),0);
            char* end=sf_mem_end();
            struct sf_block* next=(struct sf_block*)((char*)end-2*HSIZE);
            next->prev_footer=start->header;
        }
            head->body.links.prev=start;
            head->body.links.next=start;
            start->body.links.next=head;
            start->body.links.prev=head;
            char* end=sf_mem_end();
            struct sf_block* epilogue=(struct sf_block*)((char*)end-2*HSIZE);
            epilogue->prev_footer=start->header;
            //check if we stil need more space
            while(size_needed > current_size)
            {
                char* new=sf_mem_grow();
                if(new==NULL)
                {   
                    sf_errno=ENOMEM;
                    return NULL;
                }
                current_size+=PAGE_SZ;
                struct sf_block* new_block=(struct sf_block*)(new);
                new_block->header=create(0,PAGE_SZ,0,0,0);
                start=combine_wilderness(start, new_block);//points at the fotter of prologue
            }
            end=sf_mem_end();
            epilogue=(struct sf_block*)((char*)end-2*HSIZE);
            epilogue->header=create(0,0,1,get_alloc(epilogue->prev_footer),0);
            return alloc(start,block_size,payload);
    }
    else if(b_size(head->header)<size_needed)//has block but does not have enough space
    {
        current_size+=b_size(head->header);
        struct sf_block* start=head;
        char* current=sf_mem_grow();
        if(current==NULL)
        {
            sf_errno=ENOMEM;
            return NULL;
        }
        current_size+=PAGE_SZ;
        struct sf_block* new_block=(struct sf_block*)current;
        new_block->header=create(0,PAGE_SZ,0,0,0);
        start=combine_wilderness(start,new_block);
        while(size_needed > current_size)
        {
            char* new=sf_mem_grow();
            if(new==NULL)
            {   
                sf_errno=ENOMEM;
                return NULL;
            }
            current_size+=PAGE_SZ;
            struct sf_block* new_block=(struct sf_block*)(new);
            new_block->header=create(0,PAGE_SZ,0,0,0);
            start=combine_wilderness(start, new_block);//points at the fotter of prologue
        }
        char* end=sf_mem_end();
        struct sf_block* epilogue=(struct sf_block*)((char*)end-2*HSIZE);
        epilogue->header=create(0,0,1,get_alloc(epilogue->prev_footer),0);
        return alloc(start,size_needed,payload);
    }
    else//There is enough space
    {
        return alloc(head,size_needed,payload);
    }
    sf_errno=ENOMEM;
    return NULL;
}

void sf_free(void *pp) {
    if((pp==NULL)|(((uintptr_t)pp % BOUND)!=0))
    {
        abort();
    }
    sf_block* current=(sf_block*)((char*)pp- 2*HSIZE);
    size_t size=b_size(current->header);
    size_t size_two=b_size(current->prev_footer);
    sf_block* prev=(sf_block*)((char*)current - size_two);
    sf_block* start= (sf_block*)(sf_mem_start());
    start=(sf_block*)((char*)start + MIN);
    sf_block* end= (sf_block*)((char*)sf_mem_end()-2*HSIZE);
    sf_block* next=(sf_block*)((char*)current + size);
    if((current<start)|(next>end)|(size<MIN)|(size%BOUND!=0)|(get_alloc(current->header)==0)|(get_prev_alloc(current->header)==0 && get_alloc(current->prev_footer)))
    {
       abort();
    }
    clear_prev_alloc(next);//clear the bit of next block
    total_allocated-=size;//substract the size of block from total
    total_payload-=get_payload(current->header);//substract the payload from total payload
    current->prev_footer=prev->header;
    current->header=create(0,size,0,get_alloc(current->prev_footer),0);//clear the bit and payload for current block
    sf_block* new=combine(current);
    size=b_size(new->header);
    next=(sf_block*)((char*)new + size);
    next->prev_footer=new->header;
    if(next==sf_mem_end()-2*HSIZE)
    {
        insert(new, NUM_FREE_LISTS-1);
    }
    else{
        insert(new, find(size));
    }
}

void *sf_realloc(void *pp, size_t rsize) {
    if((pp==NULL)|(((uintptr_t)pp % BOUND)!=0))
    {
       sf_errno=EINVAL;
       return NULL;
    }
    sf_block* current=(sf_block*)((char*)pp- 2*HSIZE);
    size_t size=b_size(current->header);
    sf_block* start= (sf_block*)(sf_mem_start());
    start=(sf_block*)((char*)start + MIN);
    sf_block* end= (sf_block*)((char*)sf_mem_end()-2*HSIZE);
    sf_block* next=(sf_block*)((char*)current + size);
    if((current<start)|(next>end)|(size<MIN)|(size%BOUND!=0)|(get_alloc(current->header)==0)|(get_prev_alloc(current->header)==0 && get_alloc(current->prev_footer)))
    {
       sf_errno=EINVAL;
       return NULL;
    }
    if(rsize==0)
    {
        sf_free(pp);
        return NULL;
    }
    size_t size_needed=MIN;
    if(rsize + 16 > MIN)
    {
        size_needed=((rsize + BOUND)+BOUND-1) & ~(0xf);
    }
    // Reallocating larger blocks:
    if(size_needed > size)
    {
        void* result = sf_malloc(rsize);
        memcpy(result, pp, get_payload(current->header));
        sf_free(pp);
        return result;
    }
    else // reallocating for smaller blocks
    {
        // No need to split
        size_t difference=size-size_needed;
        if((difference) < MIN)
        {
            if(rsize > get_payload(current->header))//larger size but can use the same block
            {
                total_payload+=(rsize-get_payload(current->header));
                if(max_aggregate<total_payload)
                {
                    max_aggregate=total_payload;
                }
            }
            else{//smaller size
                total_payload-=(get_payload(current->header)-rsize);
            }
            current->header=create(rsize, size, 1, get_prev_alloc(current->header),0);
            next->prev_footer=current->header;
        }
        else //split the block
        {
            total_allocated-=difference;
            total_payload-=(get_payload(current->header)-rsize);
            current->header=create(rsize,size_needed, 1, get_prev_alloc(current->header),0);
            sf_block* next_block=(sf_block*)((char*)current+ size_needed);
            next_block->prev_footer=current->header;
            next_block->header=create(0,difference,0,1,0);
            sf_block* footer=(sf_block*)((char*)next_block+ difference);
            footer->prev_footer=next_block->header;
            clear_prev_alloc(footer);
            next_block=combine(next_block);
            size_t s=b_size(next_block->header);
            footer=(sf_block*)((char*)next_block + s);
            footer->prev_footer=next_block->header;
            if(footer==sf_mem_end()-2*HSIZE)
            {
                insert(next_block, NUM_FREE_LISTS-1);
            }
            else
            {
                insert(next_block, find(s));
            }
        }
    }
    return pp;
}

double sf_fragmentation() {
    if(total_allocated==0)
    {
        return 0.0;
    }
    return ((double)total_payload/(double)total_allocated);
}

double sf_utilization() {
    if(init_state==0)
    {
        return 0.0;
    }
    size_t heap_size=sf_mem_end()-sf_mem_start();
    return ((double)max_aggregate/(double)heap_size);
}
