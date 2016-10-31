//
//  COMP1927 Assignment 1 - Vlad: the memory allocator
//  allocator.c ... implementation
//
//  Created by Liam O'Connor on 18/07/12.
//  Modified by John Shepherd in August 2014, August 2015
//  Copyright (c) 2012-2015 UNSW. All rights reserved.
//

#include "allocator.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define FREE_HEADER_SIZE  sizeof(struct free_list_header)  
#define ALLOC_HEADER_SIZE sizeof(struct alloc_block_header)  
#define MAGIC_FREE     0xDEADBEEF
#define MAGIC_ALLOC    0xBEEFDEAD

#define BEST_FIT       1
#define WORST_FIT      2
#define RANDOM_FIT     3

#define MINIMUM_SIZE 1024
#define FREE_TYPECAST free_header_t *
#define MINIMUM_BLOCK_SIZE 8
#define SOME_STUPID_LARGE_NUMBER 1094967288

typedef unsigned char byte;
typedef u_int32_t vsize_t;
typedef u_int32_t vlink_t;
typedef u_int32_t vaddr_t;

typedef struct free_list_header {
   u_int32_t magic;  // ought to contain MAGIC_FREE
   vsize_t size;     // # bytes in this block (including header)
   vlink_t next;     // memory[] index of next free block
   vlink_t prev;     // memory[] index of previous free block
} free_header_t;

typedef free_header_t *Free_header;

typedef struct alloc_block_header {
   u_int32_t magic;  // ought to contain MAGIC_ALLOC
   vsize_t size;     // # bytes in this block (including header)
} alloc_header_t;


//typedef free_header_t *Free_header;

// Global data

static byte *memory = NULL;   // pointer to start of allocator memory
static vaddr_t free_list_ptr; // index in memory[] of first block in free list
static vsize_t memory_size;   // number of bytes malloc'd in memory[]
static u_int32_t strategy;    // allocation strategy (by default BEST_FIT)

// Private functions

static void vlad_merge();


// Input: size - number of bytes to make available to the allocator
// Output: none
// Precondition: Size >= 1024
// Postcondition: `size` bytes are now available to the allocator
//
// (If the allocator is already initialised, this function does nothing,
//  even if it was initialised with different size)

void vlad_init(u_int32_t size)
{
   if(memory == NULL) {

      int neededSize = size*sizeof(byte);

      // checks for size
      int givenSize = MINIMUM_SIZE;

      while(givenSize < neededSize) {
         givenSize = givenSize * 2;
      }

      memory = malloc(givenSize);

      // error for malloc failure
      if(memory == NULL) {
         fprintf(stderr, "vlad_init: Insufficient memory\n");
         exit(EXIT_FAILURE);
      }

      // initialising Global data
      memory_size = givenSize;
      free_list_ptr = 0;
      strategy = BEST_FIT;

      // initialising the free block header
      Free_header block = (FREE_TYPECAST)memory;
      block->magic = MAGIC_FREE;
      block->size = givenSize;
      block->prev = 0;
      block->next = 0;
   }

   // TODO for Milestone 1
}


// Input: n - number of bytes requested
// Output: p - a pointer, or NULL
// Precondition: n < size of largest available free block
// Postcondition: If a region of size n or greater cannot be found, p = NULL 
//                Else, p points to a location immediately after a header block
//                      for a newly-allocated region of some size >= 
//                      n + header size.

void *vlad_malloc(u_int32_t n)
{
   // chosen size to be a multiple of 4
   u_int32_t actualSize;
   if(n < MINIMUM_BLOCK_SIZE) {
      actualSize = MINIMUM_BLOCK_SIZE;
   } else if(n % 4 == 0) {
      actualSize = n;
   } else if(n > SOME_STUPID_LARGE_NUMBER) {
      actualSize = SOME_STUPID_LARGE_NUMBER;
   } else {
      actualSize = n - n%4 + 4;
   }
   actualSize = actualSize + ALLOC_HEADER_SIZE;

   // choose which free block to malloc
   Free_header chosen = (void *)(memory + free_list_ptr);
   Free_header curr = (void *) (memory + chosen->next);
   while(curr != (void *)(memory + free_list_ptr)) {
      if(curr->size < chosen->size && curr->size >= actualSize) {
         chosen = curr;
      }
      curr = (void *) (memory + curr->next);
   }

   // change chosen free block to a malloc block
   alloc_header_t *allocBlock = (alloc_header_t *)chosen;
   allocBlock->magic = MAGIC_ALLOC;

   // if under threshold just give the whole block
   if(chosen->size < (actualSize + 2 * FREE_HEADER_SIZE)){
      if(chosen->next == (void*)chosen - (void*)memory) {
         return NULL;
      }
      allocBlock->size = chosen->size;
      curr = (FREE_TYPECAST) (memory + chosen->prev);
      curr->next = chosen->next;
      curr = (FREE_TYPECAST) (memory + chosen->next);
      curr->prev = chosen->prev;
      // if chosen block was head of free list
      if(chosen == (void *)(memory) + free_list_ptr) {
         free_list_ptr = chosen->next;
      }
   } else { // if over threshold, split block into 2
      // if chosen block was the first free block changes free_list_ptr
      if(chosen == (void *) (memory) + free_list_ptr) {
         free_list_ptr = free_list_ptr + actualSize;
      }

      Free_header block = ((void *)(chosen) + actualSize);
      block->magic = MAGIC_FREE;
      block->size = chosen->size - actualSize;
      // if there is more than 1 free block
      if(chosen->next != (void*)chosen - (void*)memory) {
         block->prev = chosen->prev;
         block->next = chosen->next;
         curr = (FREE_TYPECAST) (memory + chosen->prev);
         curr->next = curr->next + actualSize;
         curr = (FREE_TYPECAST) (memory + chosen->next);
         curr->prev = curr->prev + actualSize;
      } else { // if there is only 1 free block
         block->next = free_list_ptr;
         block->prev = free_list_ptr;
      }
      allocBlock->size = actualSize;
   }

   // clear left over data from  the free block header;
   chosen->prev = 0;
   chosen->next = 0;

   // always returns the chosen block;
   return ((void*)(chosen) + ALLOC_HEADER_SIZE);

   // TODO for Milestone 2
}


// Input: object, a pointer.
// Output: none
// Precondition: object points to a location immediately after a header block
//               within the allocator's memory.
// Postcondition: The region pointed to by object has been placed in the free
//                list, and merged with any adjacent free blocks; the memory
//                space can be re-allocated by vlad_malloc

void vlad_free(void *object)
{
   // error message when they try to free a pointer outside of the initial range
   if(object < (void *) memory || object > (void *) (memory + memory_size)) {
      fprintf(stderr, "vlad_free: Attempt to free via invalid pointer\n");
      exit(EXIT_FAILURE);
   }

   // error message when they try to free something that's not an allocated
   Free_header block = object - ALLOC_HEADER_SIZE;
   if(block->magic != MAGIC_ALLOC) {
      fprintf(stderr, "vlad_free: Attempt to free non-allocated memory\n");
      exit(EXIT_FAILURE);
   }

   // memory[] index of the requested alloc block
   int position = object - (void *)memory - ALLOC_HEADER_SIZE;

   Free_header prev = (void *) (memory + free_list_ptr);
   Free_header next = (void *) (memory + free_list_ptr);

   // special case where the free block is right next to the start of the list
   if(position < block->next && position > (void*)block - (void*)memory) {

   }

   // setting up the position around the chosen block
   // the case where the chosen block is between the first and last free block
   if(position > free_list_ptr && position < prev->prev) {

      // points the prev free block to the chosen position
      // saves the position of the free block before the chosen position
      while(prev != (void *) (memory + prev->prev)) {
         if(prev->next > position) {
            prev->next = position;
            break;
         }
         prev = (void *) (memory + prev->next);
      }
      // points the next free block to the chosen position
      // saves the position of the free block after the chosen position
      next = (void*) (memory + next->prev);
      while(next != (void *) (memory + free_list_ptr)) {
         if(next->prev < position) {
            next->prev = position;
            break;
         }
         next = (void *) (memory + next->prev);
      }
   } else { // the case if the chosen block isn't between
      prev = (void *) (memory + prev->prev);
      prev->next = position;
      next->prev = position;
      if(position < free_list_ptr) {
         free_list_ptr = position;
      }
   }

   // changes the alloc block to the free block
   block->magic = MAGIC_FREE;
   block->next = (void *)next - (void *)memory;
   block->prev = (void *)prev - (void *)memory;

   // TODO for Milestone 3
   vlad_merge();
}

// Input: current state of the memory[]
// Output: new state, where any adjacent blocks in the free list
//            have been combined into a single larger block; after this,
//            there should be no region in the free list whose next
//            reference is to a location just past the end of the region
static void vlad_merge()
{
   Free_header curr = (void *)memory + free_list_ptr;
   while(curr->next != free_list_ptr) {
      if(curr->next == (void*)curr - (void*)memory + curr->size) {
         Free_header next = (void*)memory + curr->next;
         curr->size = curr->size + next->size;
         curr->next = next->next;
         curr = (void*)memory + curr->next;
         curr->prev = next->prev;
         next->magic = 0;
         next->size = 0;
         next->next = 0;
         next->prev = 0;
         vlad_merge();
         curr = (void *)memory + free_list_ptr;
      }
      curr = (void*)memory + curr->next;
   }
	// TODO for Milestone 4
}

// Stop the allocator, so that it can be init'ed again:
// Precondition: allocator memory was once allocated by vlad_init()
// Postcondition: allocator is unusable until vlad_int() executed again

void vlad_end(void)
{
   free(memory);
   // TODO for Milestone 1
}


// Precondition: allocator has been vlad_init()'d
// Postcondition: allocator stats displayed on stdout

void vlad_stats(void)
{
   Free_header curr = (void *) (memory + free_list_ptr);
   int position = free_list_ptr, counter = 1;
   int largestSize = curr->size - ALLOC_HEADER_SIZE;
   printf("free block %d position is %d, size is %d, prev is %d, next is %d\n",
          counter, position, curr->size, curr->prev, curr->next);
   while(curr->next != free_list_ptr) {
      curr = (void *) (memory + curr->next);
      position = (void *)curr - (void *)memory;
      counter++;
      printf("free block %d position is %d, size is %d, prev is %d, next is %d\n",
             counter, position, curr->size, curr->prev, curr->next);
      if(curr->size > largestSize) {
         largestSize = curr->size - ALLOC_HEADER_SIZE;
      }
   }
   printf("the largest size available is %d byte\n", largestSize);

//   printf("vlad_stats() won't work until vlad_malloc() works\n");
   return;
}

