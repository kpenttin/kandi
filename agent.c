#include <sys/types.h>

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <memdebug.h>
#include <stdio.h>
#include <time.h>
#include <ctype.h>
#include <malloc.h>

#include <sys/thread.h>
#include <dev/board.h>

#include <dev/urom.h>
#include <fs/uromfs.h>
#include <io.h>
#include <arpa/inet.h>

#include <pro/snmp_config.h>
#include <pro/snmp.h>
#include <pro/snmp_api.h>
//#include <pro/snmp_auth.h>

#include "snmp_auth.h"
#include <pro/snmp_mib.h>
#include <pro/snmp_agent.h>

#include "urom_data.c"

static char inbuf[128];
volatile int dataReadyToSend = 0;
SNMP_SESSION session;
int requestname = 0;
static volatile char * name;


// SOP AI
#define MAX_ACCEPTED_DIFFERENCE 1
int DATABASE_SIZE=0;
// Database declarations
typedef struct
{
	char *inputs[5];
	char *responses[5];
}SENTENCES;

typedef struct
{
	char *inputs[10][5];
	char *responses[10][5];
}WORDS;

// Function declarations
char* generateResponseUsingSentencesDb(SENTENCES * sentences_db, char* input);
char* generateResponseUsingWordsDb(WORDS * words_db, SENTENCES * sentences_db, char* input);
void parseLine (char str[]);
int stringCompare(char str1[],char str2[]);
void readDatabaseIntoMemory(SENTENCES * sentences_db, WORDS * words_db);

static char *UpdateStringEnv(char *name, char *var, char *value, size_t var_val_len)
{
	int i = 0;
	//printf("UpdateStringEnv\n");
    if (var) {
        free(var);
    }
    if ((var = malloc(var_val_len + 1)) != NULL) {
    	//printf("value: %s, strlen(value): %d\n", value,strlen(value));

    	for(i=0;i<var_val_len;i++)
    	{
    		var[i] = value[i];
    		//printf("%c\n",var[i]);
    	}
    	var[var_val_len] = '\0';
        //strcpy(var, value);
        //printf("sizeof(var): %d, strlen(var): %d\n", sizeof(var),strlen(var));
        //printf("var: %s, strlen(var): %d, var_val_len: %d\n", var,strlen(var),var_val_len);
        if (name) {
            setenv(name, value, 1);
        }
    }
    return var;
}

//static int SnmpCreateResponse(SNMP_SESSION * sess, CONST uint8_t * snmp_in, uint8_t * snmp_out, size_t snmp_length, long errstat, long errindex);

/*!
 * \addtogroup xgSNMP
 */
/*@{*/

/*
 * Using this as a global had been derived from the original CMU code.
 * It is very ugly (shiffer), but may require some effort to transform
 * it into something local.
 */
static uint8_t *packet_end;

static void SetVariable(CONST uint8_t * var_val, uint8_t var_val_type, uint8_t * statP, size_t statLen)
{
    size_t buffersize = 1000;

    switch (var_val_type) {
    case ASN_INTEGER:
    case ASN_COUNTER:
    case ASN_GAUGE:
    case ASN_TIMETICKS:
        AsnIntegerParse(var_val, &buffersize, &var_val_type, (long *) statP);
        break;
    case ASN_OCTET_STR:
    case ASN_IPADDRESS:
    case ASN_OPAQUE:
        AsnOctetStringParse(var_val, &buffersize, &var_val_type, statP, &statLen);
        break;
    case ASN_OBJECT_ID:
        AsnOidParse(var_val, &buffersize, &var_val_type, (OID *) statP, &statLen);
        break;
    }
}

/*!
 * \brief Parse a list of variables.
 *
 * \param data       Pointer to the start of the list.
 * \param length     Contains the number of valid bytes following the
 *                   start of the list.
 * \param out_data   Pointer to the output buffer.
 * \param out_length Number of bytes available in the output buffer.
 * \param index      Error index.
 * \param msgtype    Type of the incoming packet.
 * \param action     Action to perform, either SNMP_ACT_RESERVE1,
 *                   SNMP_ACT_RESERVE2, SNMP_ACT_COMMIT, SNMP_ACT_ACTION
 *                   or SNMP_ACT_FREE.
 *
 * \return 0 on success. Otherwise an error code is returned.
 *
 */
static int SnmpVarListParse(SNMP_SESSION * sess, CONST uint8_t * data, size_t length, uint8_t * out_data, size_t out_length,
                            long *index, int msgtype, int action)
{
	OID sop_base_oid[] = {
			1,	//iso
			3,	//identified-organization
			6,	//dod
			1,	//internet
			3,	//experimental
			55,
			0,
			0
	};

	OID sop_base_oid2[] = {
				1,	//iso
				3,	//identified-organization
				6,	//dod
				1,	//internet
				3,	//experimental
				55,
				0,
				1
		};

    OID var_name[MAX_OID_LEN];
    size_t var_name_len;
    size_t var_val_len;
    uint8_t var_val_type;
    uint8_t *var_val;
    uint8_t statType;
    uint8_t *statP;
    size_t statLen;
    uint16_t acl;
    int exact, err;
    WMETHOD *wmethod;
    uint8_t *headerP;
    uint8_t *var_list_start;
    size_t dummyLen;
    int noSuchObject = 0;
    int i = 0;
    int oiderror = 0;
    int oiderror2 = 0;

    exact = (msgtype != SNMP_MSG_GETNEXT);
    /* Check if the list starts with a sequence header and get its length. */
    if ((data = AsnSequenceParse(data, &length, ASN_SEQUENCE | ASN_CONSTRUCTOR)) == NULL) {
        return SNMP_PARSE_ERROR;
    }

    /* Build ASN header. */
    headerP = out_data;
    if ((out_data = AsnSequenceBuild(out_data, &out_length, ASN_SEQUENCE | ASN_CONSTRUCTOR, 0)) == NULL) {
        return SNMP_BUILD_ERROR;
    }
    var_list_start = out_data;

    *index = 1;
    while (length > 0) {
        /* Get name and ASN1 encoded value of the next variable. */
        var_name_len = MAX_OID_LEN;
        if ((data = SnmpVarParse(data, &length, var_name, &var_name_len, &var_val_type, &var_val, &var_val_len)) == NULL) {
            return SNMP_PARSE_ERROR;
        }

        if(msgtype == SNMP_MSG_RESPONSE)
		{
        	//printf("%s %d \n", (var_val+2), var_val_len);
        	for(i=0;i<var_name_len;i++)
        	{
        		//printf("%d\n",var_name[i]);
				if(var_name[i] != sop_base_oid2[i])
					oiderror2 = 1;
			}
        	if(!oiderror2){
        			name = UpdateStringEnv(NULL,name,(char*)(var_val+2),var_val_len);
        			return -1;
        	}
		}

        /* Now attempt to retrieve the variable on the local entity. */
        statP = SnmpMibFind(var_name, &var_name_len, &statType, &statLen, &acl, exact, &wmethod, &noSuchObject);

        /* Check access. */
        if (msgtype == SNMP_MSG_SET) {
        	for(i=0;i<var_name_len;i++)
        	{
        		if(var_name[i] != sop_base_oid[i])
        			oiderror = 1;

        	}
        	if(!oiderror)
        	       requestname = 1;
            /* Make sure we have write access. */
            if (acl != ACL_RWRITE) {
                return sess->sess_version == SNMP_VERSION_1 ? SNMP_ERR_NOSUCHNAME : SNMP_ERR_NOTWRITABLE;
            }
            if (wmethod == NULL) {
                if (statP == NULL) {
                    return sess->sess_version == SNMP_VERSION_1 ? SNMP_ERR_NOSUCHNAME : SNMP_ERR_NOCREATION;
                }
                /* Check if the type and value is consistent with this entity's variable. */
                if (var_val_len > statLen || var_val_type != statType) {
                    return sess->sess_version == SNMP_VERSION_1 ? SNMP_ERR_BADVALUE : SNMP_ERR_WRONGTYPE;
                }
                /* Actually do the set if necessary. */
                if (action == SNMP_ACT_COMMIT) {
                    SetVariable(var_val, var_val_type, statP, statLen);
                }
            } else {
                err = (*wmethod) (action, var_val, var_val_type, var_val_len, var_name, var_name_len);

                /*
                 * Map the SNMPv2 error codes to SNMPv1 error codes (RFC 2089).
                 */
                if (err && sess->sess_version == SNMP_VERSION_1) {
                    switch (err) {
                    case SNMP_ERR_WRONGVALUE:
                    case SNMP_ERR_WRONGENCODING:
                    case SNMP_ERR_WRONGTYPE:
                    case SNMP_ERR_WRONGLENGTH:
                    case SNMP_ERR_INCONSISTENTVALUE:
                        err = SNMP_ERR_BADVALUE;
                        break;
                    case SNMP_ERR_NOACCESS:
                    case SNMP_ERR_NOTWRITABLE:
                    case SNMP_ERR_NOCREATION:
                    case SNMP_ERR_INCONSISTENTNAME:
                    case SNMP_ERR_AUTHORIZATIONERROR:
                        err = SNMP_ERR_NOSUCHNAME;
                        break;
                    default:
                        err = SNMP_ERR_GENERR;
                        break;
                    }
                    return err;
                }
            }
        } else {
            /* Retrieve the value and place it into the outgoing packet. */
            if (statP == NULL) {
                statLen = 0;
                if (exact) {
                    if (noSuchObject) {
                        statType = SNMP_NOSUCHOBJECT;
                    } else {
                        statType = SNMP_NOSUCHINSTANCE;
                    }
                } else {
                    statType = SNMP_ENDOFMIBVIEW;
                }
            }
            out_data = SnmpVarBuild(out_data, &out_length, var_name, var_name_len, statType, statP, statLen);
            if (out_data == NULL) {
                return SNMP_ERR_TOOBIG;
            }
        }
        (*index)++;
    }

    if (msgtype != SNMP_MSG_SET) {
        /*
         * Save a pointer to the end of the packet and
         * rebuild header with the actual lengths
         */
        packet_end = out_data;
        dummyLen = packet_end - var_list_start;
        if (AsnSequenceBuild(headerP, &dummyLen, ASN_SEQUENCE | ASN_CONSTRUCTOR, dummyLen) == NULL) {
            return SNMP_ERR_TOOBIG;
        }
    }
    *index = 0;

    return 0;
}

/*!
 * \brief Clone input packet.
 *
 * Creates a packet identical to the input packet, except for the error
 * status and the error index which are set according to the specified
 * parameters.
 *
 * \return 0 upon success and -1 upon failure.
 */
static int SnmpCreateIdentical(SNMP_SESSION * sess, CONST uint8_t * snmp_in, uint8_t * snmp_out, size_t snmp_length, long errstat,
                               long errindex)
{
    uint8_t *data;
    uint8_t type;
    long dummy;
    size_t length;
    size_t headerLength;
    uint8_t *headerPtr;
    CONST uint8_t *reqidPtr;
    uint8_t *errstatPtr;
    uint8_t *errindexPtr;
    CONST uint8_t *varListPtr;

    /* Copy packet contents. */
    memcpy(snmp_out, snmp_in, snmp_length);
    length = snmp_length;
    if ((headerPtr = (uint8_t *) SnmpAuthParse(snmp_out, &length, sess->sess_id, &sess->sess_id_len, &dummy)) == NULL) {
        return -1;
    }
    sess->sess_id[sess->sess_id_len] = 0;

    if ((reqidPtr = AsnHeaderParse(headerPtr, &length, (uint8_t *) & dummy)) == NULL) {
        return -1;
    }
    headerLength = length;

    /* Request id. */
    if ((errstatPtr = (uint8_t *) AsnIntegerParse(reqidPtr, &length, &type, &dummy)) == NULL) {
        return -1;
    }
    /* Error status. */
    if ((errindexPtr = (uint8_t *) AsnIntegerParse(errstatPtr, &length, &type, &dummy)) == NULL) {
        return -1;
    }
    /* Error index. */
    if ((varListPtr = AsnIntegerParse(errindexPtr, &length, &type, &dummy)) == NULL) {
        return -1;
    }

    if ((data = AsnHeaderBuild(headerPtr, &headerLength, SNMP_MSG_RESPONSE, headerLength)) == NULL) {
        return -1;
    }
    length = snmp_length;
    type = (uint8_t) (ASN_UNIVERSAL | ASN_PRIMITIVE | ASN_INTEGER);
    if ((data = AsnIntegerBuild(errstatPtr, &length, type, &errstat)) != errindexPtr) {
        return -1;
    }
    if ((data = AsnIntegerBuild(errindexPtr, &length, type, &errindex)) != varListPtr) {
        return -1;
    }
    packet_end = snmp_out + snmp_length;

    return 0;
}



/*!
 * \brief Run SNMP agent.
 *
 * Normally runs in an endless loop, which is only left in case of an error.
 *
 * \param sock UDP socket to use.
 *
 * \return Always -1.
 */

// Laitta get:ille arvon get name
//static int SnmpCreateResponse(SNMP_SESSION * sess, CONST uint8_t * snmp_in, uint8_t * snmp_out, size_t snmp_length, long errstat,
//                               long errindex)
//{
//    uint8_t *data;
//    uint8_t type;
//    long dummy;
//    size_t length;
//    size_t headerLength;
//    uint8_t *headerPtr;
//    CONST uint8_t *reqidPtr;
//    uint8_t *errstatPtr;
//    uint8_t *errindexPtr;
//    CONST uint8_t *varListPtr;
//
//    /* Copy packet contents. */
//    memcpy(snmp_out, snmp_in, snmp_length);
//    length = snmp_length;
//    if ((headerPtr = (uint8_t *) SnmpAuthParse(snmp_out, &length, sess->sess_id, &sess->sess_id_len, &dummy)) == NULL) {
//        return -1;
//    }
//    sess->sess_id[sess->sess_id_len] = 0;
//
//    if ((reqidPtr = AsnHeaderParse(headerPtr, &length, (uint8_t *) & dummy)) == NULL) {
//        return -1;
//    }
//    headerLength = length;
//
//    /* Request id. */
//    if ((errstatPtr = (uint8_t *) AsnIntegerParse(reqidPtr, &length, &type, &dummy)) == NULL) {
//        return -1;
//    }
//    /* Error status. */
//    if ((errindexPtr = (uint8_t *) AsnIntegerParse(errstatPtr, &length, &type, &dummy)) == NULL) {
//        return -1;
//    }
//    /* Error index. */
//    if ((varListPtr = AsnIntegerParse(errindexPtr, &length, &type, &dummy)) == NULL) {
//        return -1;
//    }
//
//    if ((data = AsnHeaderBuild(headerPtr, &headerLength, SNMP_MSG_GET, headerLength)) == NULL) {
//        return -1;
//    }
//    length = snmp_length;
//    type = (uint8_t) (ASN_UNIVERSAL | ASN_PRIMITIVE | ASN_INTEGER);
//    if ((data = AsnIntegerBuild(errstatPtr, &length, type, &errstat)) != errindexPtr) {
//        return -1;
//    }
//    if ((data = AsnIntegerBuild(errindexPtr, &length, type, &errindex)) != varListPtr) {
//        return -1;
//    }
//    packet_end = snmp_out + snmp_length;
//
//    return 0;
//}

//
//int SnmpNameQuery(SNMP_SESSION * sess, CONST uint8_t * in_data, size_t in_len, uint8_t * out_data, size_t * out_len)
//{
//	long zero = 0;
//	uint8_t msgtype;
//	uint8_t type;
//	long reqid;
//	long errstat;
//	long errindex;
//	long dummyindex;
//	uint8_t *out_auth;
//	uint8_t *out_header;
//	uint8_t *out_reqid;
//	CONST uint8_t *data;
//	size_t len;
//	uint8_t getmsg;
//	getmsg = SNMP_MSG_GET;
//
//	SnmpStatsInc(SNMP_STAT_INPKTS);
//	printf("\n");
//	printf("Get version and community from the packet header.\n");
//	len = in_len;
//	printf("in_len: %d\n",in_len);
//	sess->sess_id_len = sizeof(sess->sess_id) - 1;
//	printf("sess->sess_id_len: %d\n",sess->sess_id_len);
//	if ((data = SnmpAuthParse(in_data, &len, sess->sess_id, &sess->sess_id_len, &sess->sess_version)) == NULL) {
//		SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
//		return -1;
//	}
//
//	printf("Check authentication.\n");
//	if (sess->sess_version == SNMP_VERSION_1 || sess->sess_version == SNMP_VERSION_2C) {
//		if (SnmpCommunityFind((char *) sess->sess_id, &sess->sess_read_view, &sess->sess_write_view)) {
//			/* TODO: Create SNMPv2 report. */
//			SnmpStatsInc(SNMP_STAT_INBADCOMMUNITYNAMES);
//			return -1;
//		}
//	} else {
//		/* Unsupported SNMP version. */
//		SnmpStatsInc(SNMP_STAT_INBADVERSIONS);
//		return -1;
//	}
//
//	printf("Parse request header and check type.\n");
//	if ((data = AsnHeaderParse(data, &len, &msgtype)) == NULL) {
//		SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
//		return -1;
//	}
//	if (msgtype == SNMP_MSG_GETBULK) {
//		/* SNMPv2 bulk requests are not yet supported. */
//		return -1;
//	} else if (msgtype != SNMP_MSG_GET && msgtype != SNMP_MSG_GETNEXT && msgtype != SNMP_MSG_SET) {
//		/* Bad request type. */
//		return -1;
//	}
//
//	printf("Parse request ID.\n");
//	if ((data = AsnIntegerParse(data, &len, &type, &reqid)) == NULL) {
//		SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
//		return -1;
//	}
//	printf("reqid: %lx\n", reqid);
//	printf("Parse error status.\n");
//	if ((data = AsnIntegerParse(data, &len, &type, &errstat)) == NULL) {
//		SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
//		return -1;
//	}
//	printf("errstat: %lx\n", errstat);
//	printf("Parse error index.\n");
//	if ((data = AsnIntegerParse(data, &len, &type, &errindex)) == NULL) {
//		SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
//		return -1;
//	}
//	printf("errindex: %lx\n", errindex);
//
//	/*
//	 * Now start cobbling together what is known about the output packet.
//	 * The final lengths are not known now, so they will have to be
//	 * recomputed later.
//	 */
//	out_auth = out_data;
//	if ((out_header = SnmpAuthBuild(sess, out_auth, out_len, 0)) == NULL) {
//		return -1;
//	}
//
//	//printf("out_data1 %d", out_data);
//
//	if ((out_reqid = AsnSequenceBuild(out_header, out_len, SNMP_MSG_RESPONSE, 0)) == NULL) {
//		return -1;
//	}
//	/* Return identical request ID. */
//	type = (uint8_t) (ASN_UNIVERSAL | ASN_PRIMITIVE | ASN_INTEGER);
//	if ((out_data = AsnIntegerBuild(out_reqid, out_len, type, &reqid)) == NULL) {
//		return -1;
//	}
//
//	//printf("out_data2 %d", out_data);
//
//	/* Assume that error status will be zero. */
//	if ((out_data = AsnIntegerBuild(out_data, out_len, type, &zero)) == NULL) {
//		return -1;
//	}
//	/* Assume that error index will be zero. */
//	if ((out_data = AsnIntegerBuild(out_data, out_len, type, &zero)) == NULL) {
//		return -1;
//	}
//
//	//printf("out_data3 %d", out_data);
//
//	/*
//	 * Walk through the list of variables and retrieve each one,
//	 * placing its value in the output packet.
//	 *
//	 * TODO: Handle bulk requests.
//	 */
//	errstat = SnmpVarListParse(sess, data, len, out_data, *out_len, &errindex, msgtype, SNMP_ACT_RESERVE1);
//
//	/*
//	 * Sets require 3 to 4 passes through the var_op_list. The first two
//	 * passes verify that all types, lengths, and values are valid and
//	 * may reserve resources and the third does the set and a fourth
//	 * executes any actions. Then the identical GET RESPONSE packet is
//	 * returned.
//	 *
//	 * If either of the first two passes returns an error, another pass
//	 * is made so that any reserved resources can be freed.
//	 */
//	if (msgtype == SNMP_MSG_SET) {
//		if (errstat == 0) {
//			errstat = SnmpVarListParse(sess, data, len, out_data, *out_len, &errindex, getmsg, SNMP_ACT_RESERVE2);
//		}
//		if (errstat == 0) {
//			errstat = SnmpVarListParse(sess, data, len, out_data, *out_len, &dummyindex, getmsg, SNMP_ACT_COMMIT);
//			SnmpVarListParse(sess, data, len, out_data, *out_len, &dummyindex, getmsg, errstat ? SNMP_ACT_FREE : SNMP_ACT_ACTION);
//			if (SnmpCreateIdentical(sess, in_data, out_auth, in_len, 0L, 0L)) {
//				return -1;
//			}
//			*out_len = packet_end - out_auth;
//			return 0;
//		} else {
//			SnmpVarListParse(sess, data, len, out_data, *out_len, &dummyindex, getmsg, SNMP_ACT_FREE);
//		}
//	}
//
//	if (errstat) {
//		/* Create an error response. */
//		if (SnmpCreateIdentical(sess, in_data, out_auth, in_len, errstat, errindex)) {
//			return -1;
//		}
//		*out_len = packet_end - out_auth;
//		return 0;
//	}
//
//	/*
//	 * Re-encode the headers with the real lengths.
//	 */
//	*out_len = packet_end - out_header;
//	out_data = AsnSequenceBuild(out_header, out_len, getmsg, packet_end - out_reqid);
//	if (out_data != out_reqid) {
//		return -1;
//	}
//	*out_len = packet_end - out_auth;
//	out_data = SnmpAuthBuild(sess, out_auth, out_len, packet_end - out_header);
//	*out_len = packet_end - out_auth;
//
//	printf("end of SNMPNameQuery\n");
//
//	return 0;
//}
//int SnmpAgent(UDPSOCKET * sock)
//{
//    int rc = -1;
//    uint32_t raddr;
//    uint16_t rport;
//    size_t out_len;
//    uint8_t *in_data = malloc(SNMP_MAX_LEN);
//    uint8_t *out_data = malloc(SNMP_MAX_LEN);
//    SNMP_SESSION *sess = malloc(sizeof(SNMP_SESSION));
//
//    if (in_data && out_data && sess) {
//        for (;;)
//        {
//            rc = NutUdpReceiveFrom(sock, &raddr, &rport, in_data, SNMP_MAX_LEN, 0);
//            // N�yt� tullut viesti
//            //char *str = "";
//            //str = getMessage();
//            //printf("message is: %s\n",str);
//            if (rc < 0) {
//                break;
//            }
//            out_len = SNMP_MAX_LEN;
//            memset(sess, 0, sizeof(SNMP_SESSION));
//            int arrd = inet_addr("10.10.10.100");
//            int prot = 161;
//            sess->sess_rem_addr = arrd;
//            sess->sess_rem_port = prot;
//			// Lue input
//            //char input[50];
//            //fgets(input,49,stdin);
//            //printf("input on %s\n",input);
//
//
//            /*if (SnmpNameQuery(sess, in_data, (size_t) rc, out_data, &out_len) == 0) {
//            	if (NutUdpSendTo(sock, raddr, rport, out_data, out_len) == 0) {
//            	                    SnmpStatsInc(SNMP_STAT_OUTPKTS);
//            	}
//            }*/
//
//            if (SnmpAgentProcessRequest(sess, in_data, (size_t) rc, out_data, &out_len) == 0) {
//                if (NutUdpSendTo(sock, raddr, rport, out_data, out_len) == 0) {
//                    SnmpStatsInc(SNMP_STAT_OUTPKTS);
//                }
//                CreateRequest(sess);
//            }
//        }
//    } else {
//        rc = -1;
//    }
//    if (in_data) {
//        free(in_data);
//    }
//    if (out_data) {
//        free(out_data);
//    }
//    if (sess) {
//        free(sess);
//    }
//    return rc;
//}

/*!
 * \brief Parse incoming and create outgoing packet.
 *
 * \param in_data  Pointer to the incoming packet.
 * \param in_len   Number of valid bytes in the incoming packet.
 * \param out_data Pointer to a buffer for the outgoing packet.
 * \param out_len  Pointer to the variable that receives the number of
 *                 bytes in the outgoing packet.
 * \param out_len  Pointer to a variable which contains the size of the
 *                 output buffer on entry. On exit, it is returned
 *                 as the number of valid bytes in the output buffer.
 *
 * \return 0 upon success and -1 upon failure.
 */
int SnmpProcessRequest(SNMP_SESSION * sess, CONST uint8_t * in_data, size_t in_len, uint8_t * out_data, size_t * out_len)
{
    long zero = 0;
    uint8_t msgtype;
    uint8_t type;
    long reqid;
    long errstat;
    long errindex;
    long dummyindex;
    uint8_t *out_auth;
    uint8_t *out_header;
    uint8_t *out_reqid;
    CONST uint8_t *data;
    size_t len;

    SnmpStatsInc(SNMP_STAT_INPKTS);
    /* Get version and community from the packet header. */
    len = in_len;
    sess->sess_id_len = sizeof(sess->sess_id) - 1;
    if ((data = SnmpAuthParse(in_data, &len, sess->sess_id, &sess->sess_id_len, &sess->sess_version)) == NULL) {
        SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
        return -1;
    }

    /* Check authentication. */
    if (sess->sess_version == SNMP_VERSION_1 || sess->sess_version == SNMP_VERSION_2C) {
        if (SnmpCommunityFind((char *) sess->sess_id, &sess->sess_read_view, &sess->sess_write_view)) {
            /* TODO: Create SNMPv2 report. */
            SnmpStatsInc(SNMP_STAT_INBADCOMMUNITYNAMES);
            return -1;
        }
    } else {
        /* Unsupported SNMP version. */
        SnmpStatsInc(SNMP_STAT_INBADVERSIONS);
        return -1;
    }

    /* Parse request header and check type. */
    if ((data = AsnHeaderParse(data, &len, &msgtype)) == NULL) {
        SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
        return -1;
    }
    if (msgtype == SNMP_MSG_GETBULK) {
        /* SNMPv2 bulk requests are not yet supported. */
        return -1;
    } else if (msgtype != SNMP_MSG_GET && /*msgtype != SNMP_MSG_GETNEXT &&*/ msgtype != SNMP_MSG_SET && msgtype != SNMP_MSG_RESPONSE) {
        /* Bad request type. */
        return -1;
    }

    /* Parse request ID. */
    if ((data = AsnIntegerParse(data, &len, &type, &reqid)) == NULL) {
        SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
        return -1;
    }
    /* Parse error status. */
    if ((data = AsnIntegerParse(data, &len, &type, &errstat)) == NULL) {
        SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
        return -1;
    }
    /* Parse error index. */
    if ((data = AsnIntegerParse(data, &len, &type, &errindex)) == NULL) {
        SnmpStatsInc(SNMP_STAT_INASNPARSEERRS);
        return -1;
    }

    /*
     * Now start cobbling together what is known about the output packet.
     * The final lengths are not known now, so they will have to be
     * recomputed later.
     */
    out_auth = out_data;
    if ((out_header = SnmpAuthBuild(sess, out_auth, out_len, 0)) == NULL) {
        return -1;
    }

    //printf("out_data1 %d", out_data);

    if ((out_reqid = AsnSequenceBuild(out_header, out_len, SNMP_MSG_RESPONSE, 0)) == NULL) {
        return -1;
    }
    /* Return identical request ID. */
    type = (uint8_t) (ASN_UNIVERSAL | ASN_PRIMITIVE | ASN_INTEGER);
    if ((out_data = AsnIntegerBuild(out_reqid, out_len, type, &reqid)) == NULL) {
        return -1;
    }

    //printf("out_data2 %d", out_data);

    /* Assume that error status will be zero. */
    if ((out_data = AsnIntegerBuild(out_data, out_len, type, &zero)) == NULL) {
        return -1;
    }
    /* Assume that error index will be zero. */
    if ((out_data = AsnIntegerBuild(out_data, out_len, type, &zero)) == NULL) {
        return -1;
    }

    //printf("out_data3 %d", out_data);

    /*
     * Walk through the list of variables and retrieve each one,
     * placing its value in the output packet.
     *
     * TODO: Handle bulk requests.
     */
    errstat = SnmpVarListParse(sess, data, len, out_data, *out_len, &errindex, msgtype, SNMP_ACT_RESERVE1);

    if(msgtype == SNMP_MSG_RESPONSE)
    {
        	    	//printf("response received\n");
        	    	return -1;
    }
    /*
     * Sets require 3 to 4 passes through the var_op_list. The first two
     * passes verify that all types, lengths, and values are valid and
     * may reserve resources and the third does the set and a fourth
     * executes any actions. Then the identical GET RESPONSE packet is
     * returned.
     *
     * If either of the first two passes returns an error, another pass
     * is made so that any reserved resources can be freed.
     */
    if (msgtype == SNMP_MSG_SET) {
        if (errstat == 0) {
            errstat = SnmpVarListParse(sess, data, len, out_data, *out_len, &errindex, msgtype, SNMP_ACT_RESERVE2);
        }
        if (errstat == 0) {
            errstat = SnmpVarListParse(sess, data, len, out_data, *out_len, &dummyindex, msgtype, SNMP_ACT_COMMIT);
            SnmpVarListParse(sess, data, len, out_data, *out_len, &dummyindex, msgtype, errstat ? SNMP_ACT_FREE : SNMP_ACT_ACTION);
            if (SnmpCreateIdentical(sess, in_data, out_auth, in_len, 0L, 0L)) {
                return -1;
            }
            *out_len = packet_end - out_auth;
            return 0;
        } else {
            SnmpVarListParse(sess, data, len, out_data, *out_len, &dummyindex, msgtype, SNMP_ACT_FREE);
        }
    }

    if (errstat) {
        /* Create an error response. */
        if (SnmpCreateIdentical(sess, in_data, out_auth, in_len, errstat, errindex)) {
            return -1;
        }
        *out_len = packet_end - out_auth;
        return 0;
    }

    /*
     * Re-encode the headers with the real lengths.
     */
    *out_len = packet_end - out_header;
    out_data = AsnSequenceBuild(out_header, out_len, SNMP_MSG_RESPONSE, packet_end - out_reqid);
    if (out_data != out_reqid) {
        return -1;
    }
    *out_len = packet_end - out_auth;
    out_data = SnmpAuthBuild(sess, out_auth, out_len, packet_end - out_header);
    *out_len = packet_end - out_auth;
//printf("End of process\n");
    return 0;
}

SNMP_SESSION *SnmpOpenSession(uint32_t ip, uint16_t port, uint8_t * id, size_t idlen, UDPSOCKET *sock)
{
     SNMP_SESSION *session = calloc(1, sizeof(SNMP_SESSION));

     if (session) {
         /* Create UDP socket at random local port. */
         session->sess_sock = sock;
         if (session->sess_sock == NULL) {
             /* Failed to create socket. */
             free(session);
             session = NULL;
         } else {
             /* Set remote address/port. */
             session->sess_rem_addr = ip;
             session->sess_rem_port = port;
             /* Set session identifier. */
             memcpy(session->sess_id, id, idlen);
             session->sess_id_len = idlen;
         }
     }
     return session;
}

void SendMessage(SNMP_SESSION * sess, UDPSOCKET *sock)
{
	OID sop_base_oid[] = {
			1,	//iso
			3,	//identified-organization
			6,	//dod
			1,	//internet
			3,	//experimental
			55,
			0,
			0
	};
	sess = SnmpOpenSession(inet_addr("255.255.255.255"),SNMP_PORT,"public", 6,sock);
	SNMP_PDU *pd = SnmpPduCreate(SNMP_MSG_SET,sop_base_oid,8);
	SnmpPduAddVariable(pd,sop_base_oid,8,ASN_OCTET_STR,inbuf,strlen(inbuf));

	SnmpSessionSendPdu(sess, pd);
}

void RequestName(SNMP_SESSION * sess, UDPSOCKET *sock)
{
    uint32_t raddr;
    uint16_t rport;
	OID sop_base_oid[] = {
			1,	//iso
			3,	//identified-organization
			6,	//dod
			1,	//internet
			3,	//experimental
			55,
			0,
			1
	};
	raddr = sess->sess_rem_addr;
	rport = sess->sess_rem_port;
	SNMP_SESSION * sessi;
	sessi = SnmpOpenSession(inet_addr("255.255.255.255"),SNMP_PORT,"public", 6,sock);
	sessi->sess_rem_addr=raddr;
	sessi->sess_rem_port=rport;
	SNMP_PDU *pd = SnmpPduCreate(SNMP_MSG_GET,sop_base_oid,8);
	SnmpPduAddVariable(pd,sop_base_oid,8,ASN_NULL,NULL,0);
	SnmpSessionSendPdu(sessi, pd);
}


/*!
 * \brief Run SNMP agent.
 *
 * Normally runs in an endless loop, which is only left in case of an error.
 *
 * \param sock UDP socket to use.
 *
 * \return Always -1.
 */

/*************************************************************************
* Function to read data from file into structure
**************************************************************************/
void readDatabaseIntoMemory(SENTENCES * sentences_db, WORDS * words_db)
{

	FILE *fp = fopen("UROM:database.txt","r");
	char buffer[100];

	// 0 is '$', 1 is '@'
	int previous_type=0;
	int current_type=0;
	int i=0,j=0,z=0,k=0,index=0;
	int sentence_len=0;

	while(fgets(buffer,99,fp)!=NULL)
	{
		if (buffer[0]=='$')
			current_type=0;
		else
			current_type=1;

		char *p1=buffer,*p2=buffer;
		// Remove $ or @ from string
		p1++;
		while(*p1!=0)
		{
		*p2++ = *p1++;
		}
		*p2=0;

		// Allocate memory for sentence, copy buffer content into it & remove newline
		sentence_len = strlen(buffer);
		char* sentence = malloc(sentence_len);
		strcpy(sentence,buffer);
		sentence[strlen(sentence)-1]='\0';

		// Put sentence and words into correct slots in databases
		if(current_type==0)
		{
			if(previous_type==1)
			{
				i++;
				j=0;
			}

			// Sentences input database
			sentences_db[i].inputs[j]=sentence;
			printf("sentences inputs %s\n",sentences_db[i].inputs[j]);

			// Words input database
			k=0,index=0;
			for(z=0;z<strlen(buffer);z++)
			{

				if(*(buffer+z)==' ')
				{
					char * word=strndup(buffer+index,z-index);
					words_db[i].inputs[j][k]=word;
					k++;
					index=z+1;
				}
			}
			char * word=strndup(buffer+index,strlen(buffer)-index-1);
			words_db[i].inputs[j][k]=word;

			j++;
		}

		else
		{
			if(previous_type==0)
				j=0;

			// Sentences response database
			sentences_db[i].responses[j]=sentence;
			printf("sentences responces %s\n",sentences_db[i].responses[j]);

			// Words responses database
			k=0,index=0;
			for(z=0;z<strlen(buffer);z++)
			{

				if(*(buffer+z)==' ')
				{
					char * word=strndup(buffer+index,z-index);
					words_db[i].responses[j][k]=word;
					k++;
					index=z+1;
				}
			}
			char * word=strndup(buffer+index,strlen(buffer)-index-1);
			words_db[i].responses[j][k]=word;

			j++;
		}

		previous_type=current_type;
	}
printf("databasen luennassa i = %d\n",i);

	DATABASE_SIZE = i;
	fclose(fp);
}

/*************************************************************************
* Function to normalize inputs to comparable form
**************************************************************************/
void parseLine (char str[])
{

	// Remove newline from fgets
	str[strlen(str)-1]='\0';

	// All letters to lowercase
	int i,ch;
	for(i=0;i<strlen(str);i++)
	{
		ch=tolower(str[i]);
		str[i] = ch;
	}

	// Remove characters which are not letter or digit
	char *p1 = str;
	char *p2 = str;
	while (*p1 !=0)
	{
		if(ispunct(*p1))
			++p1;
		else
			*p2++ = *p1++;
	}
	*p2 =0;
}




/**************************************************************************
* Function to find response from sentence database
*****************************************************************************/
char* generateResponseUsingSentencesDb(SENTENCES * sentences_db, char* input)
{
	int i,j,k;
	k = rand() % 2;

	for(i=0;i<5;i++)
	{


		if(sentences_db[i].inputs[0]==0)
			{printf("i:%d\n",i);break;}

		for(j=0;j<5;j++)
		{
			if(sentences_db[i].inputs[j]==0)
				{printf("j:%d\n",j);goto loopstart;}

			printf("i:%d j%d\n",i,j);
			if(levenshtein_distance(sentences_db[i].inputs[j], input)<=MAX_ACCEPTED_DIFFERENCE)
			{
				//response = sentences_db[i].responses[k];
				printf("levenseith vastaus : %s\n",sentences_db[i].responses[k]);
				printf("input: %s \n",input);
				printf("i:%d j:%d k:%d\n",i,j,k);
				return (sentences_db[i].responses[k]);

			}			//printf("difference is: %d\n",stringCompare(sentences_db[i].inputs[j],input));
			/*if (stringCompare(sentences_db[i].inputs[j], input)<MAX_ACCEPTED_DIFFERENCE)
			{
				//response = sentences_db[i].responses[k];
				return (sentences_db[i].responses[k]);
			}*/
		}
		loopstart:
		j++;
		j--;
	}
	return ("[][][]");
}

/**************************************************************************
* Function to find response from words database
*****************************************************************************/

char* generateResponseUsingWordsDb(WORDS * words_db, SENTENCES * sentences_db, char* input)
{
	int i,k,z,g,j=0,index=0,match_ctr=0,best_match_ctr=0;
	char * words[10];
	char * word;
	char * response;
	k = rand() % 3;

	// Split input into words
	for(i=0;i<strlen(input);i++)
	{
		if(*(input+i)==' ')
		{
			word=strndup(input+index,i-index);
			words[j]=word;
			j++;
			index=i+1;
		}
	}
	word=strndup(input+index,strlen(input)-index);
	words[j]=word;
	words[j+1]='\0';

	for(i=0;i<DATABASE_SIZE;i++)
	{
		if(words_db[i].inputs[0][0]==NULL)
			break;

		for(j=0;j<5;j++)
		{

			if(words_db[i].inputs[j][0]==NULL)
				break;

			for(z=0;z<10;z++)
			{
				if(words_db[i].inputs[j][z]==NULL)
					break;

				for(g=0;g<9;g++)
				{
					if(words[g]==NULL)
						break;


					if(strcmp(words[g],words_db[i].inputs[j][z])==0)
						match_ctr++;
				}

			}
			if(match_ctr > best_match_ctr)
			{
				best_match_ctr = match_ctr;
				response = sentences_db[i].responses[k];
				match_ctr=0;
			}

		}
	}

	printf("best match ctr %d\n",best_match_ctr);
	if (best_match_ctr<2)
		return("[][][]");
	else
		return (response);
}

/**************************************************************************
* Function to compare two strings, returns the amount of difference in characters
*****************************************************************************/
int stringCompare(char str1[],char str2[])
{
	int difference=-1;
	int str1_len, str2_len, i,j;
	int ctr=0;

	// Lengths
	str1_len = strlen(str1);
	str2_len = strlen(str2);

	// Difference in lengths and different characters
	difference = str1_len - str2_len;
	if(difference<0)
		i = str1_len;
	else
		i = str2_len;

		for(j=0; j<i-1;j++)
		{
			if(str1[j]!=str2[j])
				ctr++;
		}

	difference = abs(difference)+ctr;

	return(difference);
}


int levenshtein_distance(char *s,char*t)
/*Compute levenshtein distance between s and t*/
{
  //Step 1
  int k,i,j,n,m,cost,*d,distance;
  n=strlen(s);
  m=strlen(t);
  if(n!=0&&m!=0)
  {
    d=malloc((sizeof(int))*(m+1)*(n+1));
    m++;
    n++;
    //Step 2
    for(k=0;k<n;k++)
		d[k]=k;
    for(k=0;k<m;k++)
      d[k*n]=k;
    //Step 3 and 4
    for(i=1;i<n;i++)
      for(j=1;j<m;j++)
	{
        //Step 5
        if(s[i-1]==t[j-1])
          cost=0;
        else
          cost=1;
        //Step 6
        d[j*n+i]=minimum(d[(j-1)*n+i]+1,d[j*n+i-1]+1,d[(j-1)*n+i-1]+cost);
      }
    distance=d[n*m-1];
    free(d);
    return distance;
  }
  else
    return -1; //a negative return value means that one or both strings are empty.
}

int minimum(int a,int b,int c)
/*Gets the minimum of three values*/
{
  int min=a;
  if(b<min)
    min=b;
  if(c<min)
    min=c;
  return min;
}



THREAD (SNMPAgent,arg)
{
	UDPSOCKET *sock;
	sock = NutUdpCreateSocket(SNMP_PORT);
	    /* Nut/Net doesn't provide UDP datagram buffering by default. */
	    {
	        u_short max_ms = SNMP_MAX_MSG_SIZE * 2;
	        NutUdpSetSockOpt(sock, SO_RCVBUF, &max_ms, sizeof(max_ms));
	    }


	int rc = -1;
	int sc = -1;
    uint32_t raddr;
    uint16_t rport;
    uint32_t rraddr;
    uint16_t rrport;
    size_t out_len;
    int i;
    uint8_t *in_data = malloc(SNMP_MAX_LEN);
    uint8_t *out_data = malloc(SNMP_MAX_LEN);
    SNMP_SESSION *sess = malloc(sizeof(SNMP_SESSION));
    int j = 0;

    if (in_data && out_data && sess) {
        for (;;)
        {
        	requestname = 0;
        	//memset(in_data,0,SNMP_MAX_LEN);
            rc = NutUdpReceiveFrom(sock, &raddr, &rport, in_data, SNMP_MAX_LEN, 1);

            if (rc < 0) {
                printf("\nUDP socket error\n");
                break;
            }

            else if (rc == 0) {
            	// nothing on the socket
            }
            else
            {
				//printf("\nSNMP message received\n");

				out_len = SNMP_MAX_LEN;
				memset(sess, 0, sizeof(SNMP_SESSION));

				if (SnmpProcessRequest(sess, in_data, (size_t) rc, out_data, &out_len) == 0) {
					if (NutUdpSendTo(sock, raddr, rport, out_data, out_len) == 0) {
						SnmpStatsInc(SNMP_STAT_OUTPKTS);
					}
				}
            }
            if(requestname)
            {
            	sess->sess_rem_addr=raddr;
            	sess->sess_rem_port=rport;
            	rraddr = 0;
            	RequestName(sess,sock);
            	j = 0;
            	for(j=0;rraddr!=raddr && j < 10; j++)
            	{
            		sc = NutUdpReceiveFrom(sock, &rraddr, &rrport, in_data, SNMP_MAX_LEN, 2);
            	}

            	if (j<10){
					out_len = SNMP_MAX_LEN;
					//memset(sess, 0, sizeof(SNMP_SESSION));

					SnmpProcessRequest(sess, in_data, (size_t) sc, out_data, &out_len);



					printf("%s: ",name);
					printf("%s\n",getMessage());
            	}
            	else
            	{
            		printf("%s\n",getMessage());
            	}
            	requestname = 0;
            }
            if (dataReadyToSend)
				{
					memset(sess, 0, sizeof(SNMP_SESSION));
					//printf("\nready to send SNMP message\n");
					SendMessage(sess,sock);
					dataReadyToSend = 0;
				}
        }
    } else {
        rc = -1;
    }
    if (in_data) {
        free(in_data);
    }
    if (out_data) {
        free(out_data);
    }
    if (sess) {
        free(sess);
    }

    NutUdpDestroySocket(sock);

    while(1); //noreturn
}

THREAD (UserConsole,arg)
{
    int got;
    int i;
    char *cp;



    /*
     * Nut/OS never expects a thread to return. So we enter an
     * endless loop here.
     */
    for (i = 0;; i++) {
        /*
         * A bit more advanced input routine is able to read a string
         * up to and including the first newline character or until a
         * specified maximum number of characters, whichever comes first.
         */
        //printf("\nAnna viesti: ");
        fflush(stdout);
        fgets(inbuf, sizeof(inbuf), stdin);

        /*
         * Chop off trailing linefeed.
         */
        cp = strchr(inbuf, '\n');
        if (cp)
            *cp = 0;

        /*
         * Streams support formatted output as well as printing strings
         * from program space.
         */
        if (inbuf[0])
        {
            printf("%s: %s!\n", getName(), inbuf);

        }
    }
}

THREAD (AI,arg)
{
		SENTENCES sentences_db[100];
		WORDS words_db[100];


		SENTENCES * sentences_db_ptr;
		sentences_db_ptr=sentences_db;

		WORDS * words_db_ptr;
		words_db_ptr=words_db;

		char previousInput[100];
		char *response="";
		char input[100];
		// Srand for rand() to work properly
		srand((unsigned)time(NULL));

		 if (NutRegisterDevice(&devUrom, 0, 0)) {
		        printf("UROM error\n");
		    }
		 //memset(sentences_db,0,sizeof(sentences_db));
		 //memset(words_db,0,sizeof(words_db));
		 int i,j;

		 for(i=0;i<100;i++)
		 {
			 for(j=0;j<5;j++)
			 {
				 sentences_db[i].inputs[j]=0;
				 sentences_db[i].responses[j]=0;
			 }
		 }


		 i=0;
		readDatabaseIntoMemory(sentences_db_ptr, words_db_ptr);

		printf("size of database: %d\n",sizeof(sentences_db)+sizeof(words_db));
		while (i!=-1)
		{
			printf("Sin�: ");
			fgets(input,99,stdin);
			printf("fgets menija input on: %s\n",input);
			parseLine(input);

			// Try to find response from sentence database
			printf("response ennenn\n");
			response = generateResponseUsingSentencesDb(sentences_db_ptr, input);
			printf("response generated\n");

			// Try to find response from word database if it was not found from sentences
			if(strcmp(response,"[][][]")==0)
				response = generateResponseUsingWordsDb(words_db_ptr, sentences_db_ptr, input);

			if (strcmp(input,"exit")==0)
				break;
			else if(strcmp(input,previousInput)==0)
			{
				printf("Bot: Mitä sä kysyt samaa kokoajan!!??\n");
				response = "()()()";
			}
			else if (strcmp(response,"[][][]")==0)
				printf("Bot: Mitä sä yrität höpöttää, puhutaan jostain muusta!\n");

			else
				printf("Bot: %s\n",response);

			// Save last input
			strcpy(previousInput,input);
			}
	}
