#!/bin/bash
# KGPR E2E Test Script
# Tests the full KGPR flow: create → review → merge

set -e

ENDPOINT="${YATA_GLOBAL_ENDPOINT:-http://localhost:3000}"

echo "=== KGPR End-to-End Test ==="
echo "Endpoint: $ENDPOINT"
echo ""

# Health check
echo "Step 0: Health check..."
HEALTH=$(curl -s "$ENDPOINT/health")
if echo "$HEALTH" | grep -q '"status":"healthy"'; then
    echo "✅ Server is healthy"
else
    echo "❌ Server is not responding"
    exit 1
fi
echo ""

# Step 1: Create KGPR
echo "Step 1: Creating KGPR..."
KGPR_RESPONSE=$(curl -sX POST "$ENDPOINT/api/v1/kgprs" \
  -H "Content-Type: application/json" \
  -d '{
    "title": "E2E Test Pattern",
    "description": "Testing KGPR flow",
    "sourceNamespace": "test.e2e",
    "labels": ["test", "e2e"],
    "diff": {
      "entities": {
        "added": [
          {"changeType": "add", "localId": "test-entity-1", "name": "TestEntity", "entityType": "class", "namespace": "test.e2e"}
        ],
        "updated": [],
        "deleted": []
      },
      "relationships": {"added": [], "updated": [], "deleted": []},
      "stats": {"entitiesAdded": 1, "entitiesUpdated": 0, "entitiesDeleted": 0, "relationshipsAdded": 0, "relationshipsUpdated": 0, "relationshipsDeleted": 0, "totalChanges": 1}
    }
  }')

KGPR_ID=$(echo "$KGPR_RESPONSE" | python3 -c "import sys,json;print(json.load(sys.stdin)['data']['id'])")
echo "✅ Created: $KGPR_ID"
echo ""

# Step 2: Review & Approve
echo "Step 2: Reviewing & approving..."
REVIEW_RESPONSE=$(curl -sX POST "$ENDPOINT/api/v1/kgprs/${KGPR_ID}/review" \
  -H "Content-Type: application/json" \
  -d '{"decision": "approve", "comment": "Automated test approval"}')

STATUS=$(echo "$REVIEW_RESPONSE" | python3 -c "import sys,json;print(json.load(sys.stdin)['data']['status'])")
if [ "$STATUS" = "approved" ]; then
    echo "✅ Status: approved"
else
    echo "❌ Expected status 'approved', got '$STATUS'"
    exit 1
fi
echo ""

# Step 3: Merge
echo "Step 3: Merging..."
MERGE_RESPONSE=$(curl -sX POST "$ENDPOINT/api/v1/kgprs/${KGPR_ID}/merge" \
  -H "Content-Type: application/json")

SUCCESS=$(echo "$MERGE_RESPONSE" | python3 -c "import sys,json;print(json.load(sys.stdin)['success'])")
if [ "$SUCCESS" = "True" ]; then
    MERGED=$(echo "$MERGE_RESPONSE" | python3 -c "import sys,json;print(json.load(sys.stdin)['data']['mergeResult']['entitiesMerged'])")
    echo "✅ Merged: $MERGED entities"
else
    echo "❌ Merge failed"
    exit 1
fi
echo ""

# Step 4: Verify
echo "Step 4: Verifying final state..."
FINAL_STATUS=$(curl -s "$ENDPOINT/api/v1/kgprs/${KGPR_ID}" | python3 -c "import sys,json;print(json.load(sys.stdin)['data']['status'])")
if [ "$FINAL_STATUS" = "merged" ]; then
    echo "✅ Final status: merged"
else
    echo "❌ Expected 'merged', got '$FINAL_STATUS'"
    exit 1
fi
echo ""

echo "==================================="
echo "✅ All tests passed!"
echo "==================================="
