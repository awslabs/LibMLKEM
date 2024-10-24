	.arch armv8.4-a

#include "common.i"

	.align	2
	.p2align 5,,15
	.globl _stou__c
	.globl stou__c
_stou__c:
stou__c:
	ASM_LOAD(x2, lC0)
	ldr	q31, [x2]
	mov	x2, 0
	.p2align 5,,15

# q31 is constant
# x0 is parameter SP
# x1 is parameter SP
#
# x2 is loop index
#
# q30 is accumulator
# q29 is working reg

L5:
	ldr	q30, [x0, x2]
	cmlt	v29.8h, v30.8h, #0
	and	v29.16b, v31.16b, v29.16b
	add	v29.8h, v30.8h, v29.8h
	str	q29, [x1, x2]

	add	x2, x2, 16

	cmp	x2, 512
	bne	L5
	ret

	.align	4
	.globl _stou__c2
	.globl stou__c2
_stou__c2:
stou__c2:
        ASM_LOAD(x2,lC0)
	ldr	q31, [x2]
	mov	x2, 0
	.p2align 5,,15

# q31 is constant
# x0 is parameter SP
# x1 is parameter SP
#
# x2 is offset into input and output arrays
#
# q30 is L1 accumulator
# q29 is L1 working reg
#
# q28 is L2 accumulator
# q27 is L2 working reg

L6:
	ldr	q30, [x0, x2]
	cmlt	v29.8h, v30.8h, #0
	and	v29.16b, v31.16b, v29.16b
	add	v29.8h, v30.8h, v29.8h
	str	q29, [x1, x2]

	add	x2, x2, 16

	ldr	q28, [x0, x2]
	cmlt	v27.8h, v28.8h, #0
	and	v27.16b, v31.16b, v27.16b
	add	v27.8h, v28.8h, v27.8h
	str	q27, [x1, x2]

	add	x2, x2, 16

	cmp	x2, 512
	bne	L6
	ret


	.align	4
	.globl _stou__c4
	.globl stou__c4
_stou__c4:
stou__c4:
	ASM_LOAD(x2,lC0)
	ldr	q31, [x2]
	mov	x2, 0
	.p2align 5,,15

# q31 is constant
# x0 is parameter SP
# x1 is parameter SP
#
# x2 is offset into input and output arrays
#
# q30 is L1 accumulator
# q29 is L1 working reg
#
# q28 is L2 accumulator
# q27 is L2 working reg
#
# q26 is L1 accumulator
# q25 is L1 working reg
#
# q24 is L2 accumulator
# q23 is L2 working reg

L7:
	ldr	q30, [x0, x2]
	cmlt	v29.8h, v30.8h, #0
	and	v29.16b, v31.16b, v29.16b
	add	v29.8h, v30.8h, v29.8h
	str	q29, [x1, x2]

	add	x2, x2, 16

	ldr	q28, [x0, x2]
	cmlt	v27.8h, v28.8h, #0
	and	v27.16b, v31.16b, v27.16b
	add	v27.8h, v28.8h, v27.8h
	str	q27, [x1, x2]

	add	x2, x2, 16

	ldr	q26, [x0, x2]
	cmlt	v25.8h, v26.8h, #0
	and	v25.16b, v31.16b, v25.16b
	add	v25.8h, v26.8h, v25.8h
	str	q25, [x1, x2]

	add	x2, x2, 16

	ldr	q24, [x0, x2]
	cmlt	v23.8h, v24.8h, #0
	and	v23.16b, v31.16b, v23.16b
	add	v23.8h, v24.8h, v23.8h
	str	q23, [x1, x2]

	add	x2, x2, 16

	cmp	x2, 512
	bne	L7
	ret


	.align	4
	.globl _stou__c4o
	.globl stou__c4o
_stou__c4o:
stou__c4o:
LFB8:
	ASM_LOAD(x2,lC0)
	ldr	q31, [x2]
	mov	x2, 0
	.p2align 5,,15

# q31 is constant
# x0 is parameter SP
# x1 is parameter SP
#
# x2 is offset into input and output arrays
#
# q30 is L1 accumulator
# q29 is L1 working reg
#
# q28 is L2 accumulator
# q27 is L2 working reg
#
# q26 is L1 accumulator
# q25 is L1 working reg
#
# q24 is L2 accumulator
# q23 is L2 working reg

L8:
	add	x3, x2, 16
	add	x4, x2, 32
	add	x5, x2, 48

	ldr	q30, [x0, x2]
	ldr	q28, [x0, x3]
	ldr	q26, [x0, x4]
	ldr	q24, [x0, x5]

	cmlt	v29.8h, v30.8h, #0
	cmlt	v27.8h, v28.8h, #0
	cmlt	v25.8h, v26.8h, #0
	cmlt	v23.8h, v24.8h, #0

	and	v29.16b, v31.16b, v29.16b
	and	v27.16b, v31.16b, v27.16b
	and	v25.16b, v31.16b, v25.16b
	and	v23.16b, v31.16b, v23.16b

	add	v29.8h, v30.8h, v29.8h
	add	v27.8h, v28.8h, v27.8h
	add	v25.8h, v26.8h, v25.8h
	add	v23.8h, v24.8h, v23.8h

	str	q29, [x1, x2]
	str	q27, [x1, x3]
	str	q25, [x1, x4]
	str	q23, [x1, x5]

	add	x2, x2, 64
	cmp	x2, 512
	bne	L8
	ret



	.align	4
lC0:
	.hword	3329
	.hword	3329
	.hword	3329
	.hword	3329
	.hword	3329
	.hword	3329
	.hword	3329
	.hword	3329
