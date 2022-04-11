// ==============================================================================
/**
 * bf-gc.c
 **/
// ==============================================================================



// ==============================================================================
// INCLUDES

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#include "gc.h"
#include "safeio.h"
// ==============================================================================



// ==============================================================================
// TYPES AND STRUCTURES

/** The header for each allocated object. */
typedef struct header {

	/** Pointer to the next header in the list. */
	struct header* next;

	/** Pointer to the previous header in the list. */
	struct header* prev;

	/** The usable size of the block (exclusive of the header itself). */
	size_t         size;

	/** Is the block allocated or free? */
	bool           allocated;

	/** Whether the block has been visited during reachability analysis. */
	bool           marked;

	/** A map of the layout of pointers in the object. */
	gc_layout_s*   layout;

} header_s;

/** A link in a linked stack of pointers, used during heap traversal. */
typedef struct ptr_link {

	/** The next link in the stack. */
	struct ptr_link* next;

	/** The pointer itself. */
	void* ptr;

} ptr_link_s;
// ==============================================================================



// ==============================================================================
// MACRO CONSTANTS AND FUNCTIONS

/** The system's page size. */
#define PAGE_SIZE sysconf(_SC_PAGESIZE)

/**
 * Macros to easily calculate the number of bytes for larger scales (e.g., kilo,
 * mega, gigabytes).
 */
#define KB(size)  ((size_t)size * 1024)
#define MB(size)  (KB(size) * 1024)
#define GB(size)  (MB(size) * 1024)

/** The virtual address space reserved for the heap. */
#define HEAP_SIZE GB(2)

/** Given a pointer to a header, obtain a `void*` pointer to the block itself. */
#define HEADER_TO_BLOCK(hp) ((void*)((intptr_t)hp + sizeof(header_s)))

/** Given a pointer to a block, obtain a `header_s*` pointer to its header. */
#define BLOCK_TO_HEADER(bp) ((header_s*)((intptr_t)bp - sizeof(header_s)))
// ==============================================================================


// ==============================================================================
// GLOBALS

/** The address of the next available byte in the heap region. */
static intptr_t free_addr  = 0;

/** The beginning of the heap. */
static intptr_t start_addr = 0;

/** The end of the heap. */
static intptr_t end_addr   = 0;

/** The head of the free list. */
static header_s* free_list_head = NULL;

/** The head of the allocated list. */
static header_s* allocated_list_head = NULL;

/** The head of the root set stack. */
static ptr_link_s* root_set_head = NULL;

/** The size of a double word. */
static int double_word_size = 16;

// ==============================================================================



// ==============================================================================
/**
 * Push a pointer onto root set stack.
 *
 * \param ptr The pointer to be pushed.
 */
void rs_push (void* ptr) {

	// Make a new link.
	ptr_link_s* link = malloc(sizeof(ptr_link_s));
	if (link == NULL) {
		ERROR("rs_push(): Failed to allocate link");
	}

	// Have it store the pointer and insert it at the front.
	link->ptr    = ptr;
	link->next   = root_set_head;
	root_set_head = link;
	
} // rs_push ()
// ==============================================================================



// ==============================================================================
/**
 * Pop a pointer from the root set stack.
 *
 * \return The top pointer being removed, if the stack is non-empty;
 *         <code>NULL</code>, otherwise.
 */
void* rs_pop () {

	// Grab the pointer from the link...if there is one.
	if (root_set_head == NULL) {
		return NULL;
	}
	void* ptr = root_set_head->ptr;

	// Remove and free the link.
	ptr_link_s* old_head = root_set_head;
	root_set_head = root_set_head->next;
	free(old_head);

	return ptr;
	
} // rs_pop ()
// ==============================================================================



// ==============================================================================
/**
 * Add a pointer to the _root set_, which are the starting points of the garbage
 * collection heap traversal.  *Only add pointers to objects that will be live
 * at the time of collection.*
 *
 * \param ptr A pointer to be added to the _root set_ of pointers.
 */
void gc_root_set_insert (void* ptr) {

	rs_push(ptr);
	
} // root_set_insert ()
// ==============================================================================



// ==============================================================================
/**
 * The initialization method.  If this is the first use of the heap, initialize it.
 */

void gc_init () {

	// Only do anything if there is no heap region (i.e., first time called).
	if (start_addr == 0) {

		DEBUG("Trying to initialize");
		
		// Allocate virtual address space in which the heap will reside. Make it
		// un-shared and not backed by any file (_anonymous_ space).  A failure to
		// map this space is fatal.
		void* heap = mmap(NULL,
					HEAP_SIZE,
					PROT_READ | PROT_WRITE,
					MAP_PRIVATE | MAP_ANONYMOUS,
					-1,
					0);
		if (heap == MAP_FAILED) {
			ERROR("Could not mmap() heap region");
		}

		// Hold onto the boundaries of the heap as a whole.
		start_addr = (intptr_t)heap;
		end_addr   = start_addr + HEAP_SIZE;
		free_addr  = start_addr;

		// DEBUG: Emit a message to indicate that this allocator is being called.
		DEBUG("bf-alloc initialized");

	}

} // gc_init ()
// ==============================================================================




// ==============================================================================
/**
 * @brief rounds up a value to the nearest multiple of a constant.
 * 
 * @param value value to round up.
 * @param multiple multiple of the constant to round up to. 
 * @return size_t the value rounded up to the passed in multiple.
 */
	size_t roundTo(size_t value, size_t multiple){
		size_t modded = value % multiple; // mods the values to get the remainder
		if (modded == 0){
			// if the modded value is equal to zero, it is a multiple.
			return value;
		}
		value += multiple - modded; // subtracts the remainder from the multiple then adds it to the value to round it up.
		return value; // returns the new value
	} // roundTo()
// ==============================================================================


// ==============================================================================
/**
 * @brief Adds the passed in node to the allocated headers linked list. Specifically,
 *        it adds the new node in the beginning of the list to get an O(1) insertion.
 * 
 * @param node the newly allocated header to add to the linked list
 */
void allocated_list_add(header_s* node){
	if (node == NULL){
		// checks if the passed in node isn't null.
		return;
	}
	// asserts that the node isn't connected to anything.
	node->prev = NULL;

	// makes node point to the head of the linked list.
	node->next = allocated_list_head;

	// makes the node after the head node point back to the current head node.
	if (node->next != NULL){
		// point back to the current node as the head.
		node->next->prev = node;
	} 
	// updates the head of the allocated list to point to the new head
	allocated_list_head = node;

	// flags the block as allocated.
	node->allocated = true;

	return;
} // allocated_list_add()
// ==============================================================================


// ==============================================================================
/**
 * @brief removes the passed in node from the allocated linked list.
 * 
 * @param node is the node to remove from the linked list.
 */
void allocated_list_remove(header_s* node){
	if (node == NULL || allocated_list_head == NULL){
		// if the passed in node does not point to anything, don't do anything.
		return;
	}
	if (node->next != NULL){ // TRUE if a next node exists
		// make the next node point to our prev point.
		node->next->prev = node->prev;
	}
	if (node->prev != NULL){ // TRUE if our node isn't the head of the list.
		// make the previous node point to our next node.
		node->prev->next = node->next;
	} else{
	// if our node was the head of the linked list, update the head.
		allocated_list_head = node->next;
	}
	// disconnect the node from the linked list.
	node->next = NULL;
	node->prev = NULL;
	
	return;
} // allocated_list_remove()
// ==============================================================================



// ==============================================================================
// COPY-AND-PASTE YOUR PROJECT-4 malloc() HERE.
//
//   Note that you may have to adapt small things.  For example, the `init()`
//   function is now `gc_init()` (above); the header is a little bit different
//   from the Project-4 one; my `allocated_list_head` may be a slightly
//   different name than the one you used.  Check the details.
void* gc_malloc (size_t size) {
// initialize the heap. If no heap space was available before (starting address was 0), 
	// create the heap space and store the starting address.
	gc_init();
	
	// if the space of what we want to initialize is 0, then initialize nothing and return a null pointer.
	if (size == 0) {
		return NULL;
	}

	// get the start of the free block
	size_t free_block_address = free_addr + sizeof(header_s); 
	
	// the new free address is the double-word aligned free block address - the size of the header.

	// gets the head node of the free pointers linked list.
	header_s* current = free_list_head;
	
	// declares a best fit block pointer. 
	header_s* best  = NULL;
	while (current != NULL) {
		// loop through the linked list.

		if (current->allocated) {
			// if one of the blocks on the free list is marked allocated, throw an error
			ERROR("Allocated block on free list", (intptr_t)current);
		}
		
		if ( (best == NULL && size <= current->size) || 
	 (best != NULL && size <= current->size && current->size < best->size) ) {
			// TRUE if the best fit block pointer is null, and the size of the current block is bigger than the passed in size 
			//argument, or if the best fit block pointer is not null, and the current block is a better fit than the best node.
			// update the best fit block pointer to point to the current node.
			best = current;
		}

		if (best != NULL && best->size == size) {
			// if our best fit block perfectly fits (same size) our passed in size, we exit the loop.
			break;
		}
		
		// update the current pointer to progress through the linked list.
		current = current->next;
		
	}

	// declares an empty pointer to allocate the new block at
	void* new_block_ptr = NULL;
	
	if (best != NULL) { // checks if we found a best fit block, or none exist.

		// manipulates the pointers of the linked list to prepare for the removal of the best node from the linked list
		// essentially the equivalent of running a remove on a linked list.
		if (best->prev == NULL) {
			// if best node is the head node of the free linked list, then update the head of the linked list 
			// to be the node (or null node) next to best 
			free_list_head   = best->next;
		} else {
			// if there is a node before best, make it point to the node after best
			best->prev->next = best->next;
		}
		if (best->next != NULL) {
			// make the node next to best (if it exists) point back to the node before best 
			best->next->prev = best->prev;
		}
		//adds the best fitting block to the allocated blocks linked list
		allocated_list_add(best);

		// gets a pointer to the actual usable chunk in the newly allocated block
		new_block_ptr   = HEADER_TO_BLOCK(best);
		
	} else {
		free_addr = roundTo(free_block_address, double_word_size) - sizeof(header_s);  

		// create a pointer to the header of the free address block we're allocating.
		header_s* header_ptr = (header_s*)free_addr;
		
		// gets a pointer to the actual usable chunk in the newly allocated block.
		new_block_ptr = HEADER_TO_BLOCK(header_ptr);

		// initializes the fields of the header struct and flags the new block as allocated.
		header_ptr->size      = size;

		// adds the newly created block to the allocated blocks linked list. 
		allocated_list_add(header_ptr);
		
		// this is the pointer of address of the next free block after allocating memory.
		intptr_t new_free_addr = (intptr_t)new_block_ptr + size;
		if (new_free_addr > end_addr) {
			// if we reach the end of the heap, return null.

			return NULL;

		} else {
			// updates the pointer to the next free block.
			free_addr = new_free_addr;

		}

	}
	// return a pointer to the newly allocated block.
	return new_block_ptr;


} // gc_malloc ()
// ==============================================================================



// ==============================================================================
// COPY-AND-PASTE YOUR PROJECT-4 free() HERE.
//
//   See above.  Small details may have changed, but the code should largely be
//   unchanged.
void gc_free (void* ptr) {

	if (ptr == NULL) {
		// if the pointer passed in doesn't point to anything, don't do anything.
		return;
	}

	// get the pointer to the header of the block.
	header_s* header_ptr = BLOCK_TO_HEADER(ptr);

	if (!header_ptr->allocated) { // TRUE if the block is already free.
		// if the block is actually free, throw an error.
		ERROR("Double-free: ", (intptr_t)header_ptr);
	}
	allocated_list_remove(header_ptr);
	// manipulates pointers to add the current block to the free blocks linked list. Equivalent to an O(1) add on a linked list.
	// add the pointer to this block to the beginning of the free blocks linked list 
	header_ptr->next = free_list_head;
	// updates the head of the linked list to point to the newly added free block to the list. 
	free_list_head   = header_ptr;
	// header pointer is the first node on the linked list.
	header_ptr->prev = NULL;
	if (header_ptr->next != NULL) {
		// if a node exists after our head node, make it point back to the newly inserted head node.
		header_ptr->next->prev = header_ptr;
	}
	// flag the header as free.
	header_ptr->allocated = false;
	
} // gc_free ()
// ==============================================================================



// ==============================================================================
/**
 * Allocate and return heap space for the structure defined by the given
 * `layout`.
 *
 * \param layout A descriptor of the fields
 * \return A pointer to the allocated block, if successful; `NULL` if unsuccessful.
 */

void* gc_new (gc_layout_s* layout) {

	// Get a block large enough for the requested layout.
	void*     block_ptr  = gc_malloc(layout->size);
	header_s* header_ptr = BLOCK_TO_HEADER(block_ptr);

	// Hold onto the layout for later, when a collection occurs.
	header_ptr->marked = false;
	header_ptr->layout = layout;
	
	return block_ptr;
	
} // gc_new ()
// ==============================================================================

/**
 * @brief Traverses the pointers array in the header_s layout object. It then pushes
 * 		  these pointers onto the stack.
 * @param header the header we are traversing the blocks into.
 */
void push_child_pointers(header_s* header){
	gc_layout_s* layout = header->layout;
	if (header->marked ){
		// if we already have marked the block, do nothing.
		return;
	}
	assert(layout != NULL);
	// traverse the pointers array and push the pointers in the object on the stack.
	for (int i = 0; i < layout->num_ptrs; i++){
		// get the handle contained within the block.
		void** child_handle = ((HEADER_TO_BLOCK(header) + layout->ptr_offsets[i]));
		// access the pointer being pointed to inside the block.
		void* child_ptr_block = *child_handle;
		// get the header to the child pointer
		header_s* child_ptr_header = BLOCK_TO_HEADER(child_ptr_block);
		if (!child_ptr_header->marked){
			// push pointer to the stack if not visited
			rs_push(child_ptr_block);
		}
	}

}


// ==============================================================================
/**
 * Traverse the heap, marking all live objects.
 */

void mark () {

	//   Adapt the pseudocode from class for a copying collector to real code here
	//   for a non-copying collector.  Do the traversal, using the linked stack of
	//   pointers that starts at `root_set_head`, setting the `marked` field on
	//   each object you reach.

	// Traverse the root set.
	while (root_set_head != NULL) {
		// get the top pointer from the root set 
		void* current_block = rs_pop();
		// get the current block's header.
		header_s* current_block_header = BLOCK_TO_HEADER(current_block);
		// push the child pointers to the stack (the pointers contained in this object)
		push_child_pointers(current_block_header);
		// mark the block
		current_block_header->marked = true;
	}
	safe_debug("/============MARKING COMPLETE============\n",0);
} // mark ()
// ==============================================================================



// ==============================================================================
/**
 * Traverse the allocated list of objects.  Free each unmarked object;
 * unmark each marked object (preparing it for the next sweep.
 */

void sweep () {
	// WRITE ME
	//
	//   Walk the allocated list.  Each object that is marked is alive, so clear
	//   its mark.  Each object that is unmarked is dead, so free it with
	//   `gc_free()`.
	int freed_counter = 0;
	int live_counter = 0;
	header_s* current =  allocated_list_head;
	// traverse the allocated blocks list. 
	while (current != NULL){
		if (current->marked){
			// unmark marked blocks
			current->marked = false;
			current = current->next;
			live_counter++;
		}else{
			void* ptr_to_free = HEADER_TO_BLOCK(current);
			// update pointer to current before freeing node.
			current = current->next;
			// free unmarked blocks
			gc_free(ptr_to_free);
			freed_counter++;
		}
	}	
		safe_debug("Swept number of blocks.",1,freed_counter);
		safe_debug("Kept  number of blocks.",1,live_counter);
		safe_debug("/============SWEEPING COMPLETE============\n",0);




} // sweep ()
// ==============================================================================



// ==============================================================================
/**
 * Garbage collect the heap.  Traverse and _mark_ live objects based on the
 * _root set_ passed, and then _sweep_ the unmarked, dead objects onto the free
 * list.  This function empties the _root set_.
 */

void gc () {

	// Traverse the heap, marking the objects visited as live.
	mark();

	// And then sweep the dead objects away.
	sweep();

	// Sanity check:  The root set should be empty now.
	assert(root_set_head == NULL);
	
} // gc ()
// ==============================================================================
