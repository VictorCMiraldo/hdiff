/*
 * Licensed to Elasticsearch under one or more contributor
 * license agreements. See the NOTICE file distributed with
 * this work for additional information regarding copyright
 * ownership. Elasticsearch licenses this file to you under
 * the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */


package org.elasticsearch.action.support.replication;

import org.elasticsearch.Version;
import org.elasticsearch.cluster.ClusterName;
import org.elasticsearch.cluster.ClusterState;
import org.elasticsearch.cluster.metadata.IndexMetaData;
import org.elasticsearch.cluster.metadata.MetaData;
import org.elasticsearch.cluster.node.DiscoveryNode;
import org.elasticsearch.cluster.node.DiscoveryNodes;
import org.elasticsearch.cluster.routing.IndexRoutingTable;
import org.elasticsearch.cluster.routing.IndexShardRoutingTable;
import org.elasticsearch.cluster.routing.RoutingTable;
import org.elasticsearch.cluster.routing.ShardRoutingState;
import org.elasticsearch.cluster.routing.TestShardRouting;
import org.elasticsearch.cluster.routing.UnassignedInfo;
import org.elasticsearch.common.settings.Settings;
import org.elasticsearch.common.transport.DummyTransportAddress;
import org.elasticsearch.index.shard.ShardId;

import java.util.HashSet;
import java.util.Set;

import static org.elasticsearch.cluster.metadata.IndexMetaData.SETTING_CREATION_DATE;
import static org.elasticsearch.cluster.metadata.IndexMetaData.SETTING_NUMBER_OF_REPLICAS;
import static org.elasticsearch.cluster.metadata.IndexMetaData.SETTING_NUMBER_OF_SHARDS;
import static org.elasticsearch.cluster.metadata.IndexMetaData.SETTING_VERSION_CREATED;
import static org.elasticsearch.test.ESTestCase.randomFrom;
import static org.elasticsearch.test.ESTestCase.randomIntBetween;

/**
 * Helper methods for generating cluster states
 */
public class ClusterStateCreationUtils {


    /**
     * Creates cluster state with and index that has one shard and #(replicaStates) replicas
     *
     * @param index              name of the index
     * @param activePrimaryLocal if active primary should coincide with the local node in the cluster state
     * @param primaryState       state of primary
     * @param replicaStates      states of the replicas. length of this array determines also the number of replicas
     */
    public static ClusterState state(String index, boolean activePrimaryLocal, ShardRoutingState primaryState, ShardRoutingState... replicaStates) {
        final int numberOfReplicas = replicaStates.length;

        int numberOfNodes = numberOfReplicas + 1;
        if (primaryState == ShardRoutingState.RELOCATING) {
            numberOfNodes++;
        }
        for (ShardRoutingState state : replicaStates) {
            if (state == ShardRoutingState.RELOCATING) {
                numberOfNodes++;
            }
        }
        numberOfNodes = Math.max(2, numberOfNodes); // we need a non-local master to test shard failures
        final ShardId shardId = new ShardId(index, "_na_", 0);
        DiscoveryNodes.Builder discoBuilder = DiscoveryNodes.builder();
        Set<String> unassignedNodes = new HashSet<>();
        for (int i = 0; i < numberOfNodes + 1; i++) {
            final DiscoveryNode node = newNode(i);
            discoBuilder = discoBuilder.put(node);
            unassignedNodes.add(node.id());
        }
        discoBuilder.localNodeId(newNode(0).id());
        discoBuilder.masterNodeId(newNode(1).id()); // we need a non-local master to test shard failures
        IndexMetaData indexMetaData = IndexMetaData.builder(index).settings(Settings.builder()
                .put(SETTING_VERSION_CREATED, Version.CURRENT)
                .put(SETTING_NUMBER_OF_SHARDS, 1).put(SETTING_NUMBER_OF_REPLICAS, numberOfReplicas)
                .put(SETTING_CREATION_DATE, System.currentTimeMillis())).build();

        RoutingTable.Builder routing = new RoutingTable.Builder();
        routing.addAsNew(indexMetaData);
        IndexShardRoutingTable.Builder indexShardRoutingBuilder = new IndexShardRoutingTable.Builder(shardId);

        String primaryNode = null;
        String relocatingNode = null;
        UnassignedInfo unassignedInfo = null;
        if (primaryState != ShardRoutingState.UNASSIGNED) {
            if (activePrimaryLocal) {
                primaryNode = newNode(0).id();
                unassignedNodes.remove(primaryNode);
            } else {
                Set<String> unassignedNodesExecludingPrimary = new HashSet<>(unassignedNodes);
                unassignedNodesExecludingPrimary.remove(newNode(0).id());
                primaryNode = selectAndRemove(unassignedNodesExecludingPrimary);
            }
            if (primaryState == ShardRoutingState.RELOCATING) {
                relocatingNode = selectAndRemove(unassignedNodes);
            }
        } else {
            unassignedInfo = new UnassignedInfo(UnassignedInfo.Reason.INDEX_CREATED, null);
        }
        indexShardRoutingBuilder.addShard(TestShardRouting.newShardRouting(index, 0, primaryNode, relocatingNode, null, true, primaryState, unassignedInfo));

        for (ShardRoutingState replicaState : replicaStates) {
            String replicaNode = null;
            relocatingNode = null;
            unassignedInfo = null;
            if (replicaState != ShardRoutingState.UNASSIGNED) {
                assert primaryNode != null : "a replica is assigned but the primary isn't";
                replicaNode = selectAndRemove(unassignedNodes);
                if (replicaState == ShardRoutingState.RELOCATING) {
                    relocatingNode = selectAndRemove(unassignedNodes);
                }
            } else {
                unassignedInfo = new UnassignedInfo(UnassignedInfo.Reason.INDEX_CREATED, null);
            }
            indexShardRoutingBuilder.addShard(
                    TestShardRouting.newShardRouting(index, shardId.id(), replicaNode, relocatingNode, null, false, replicaState, unassignedInfo));
        }

        ClusterState.Builder state = ClusterState.builder(new ClusterName("test"));
        state.nodes(discoBuilder);
        state.metaData(MetaData.builder().put(indexMetaData, false).generateClusterUuidIfNeeded());
        state.routingTable(RoutingTable.builder().add(IndexRoutingTable.builder(indexMetaData.getIndex()).addIndexShard(indexShardRoutingBuilder.build())).build());
        return state.build();
    }

    /**
     * Creates cluster state with several shards and one replica and all shards STARTED.
     */
    public static ClusterState stateWithAssignedPrimariesAndOneReplica(String index, int numberOfShards) {

        int numberOfNodes = 2; // we need a non-local master to test shard failures
        DiscoveryNodes.Builder discoBuilder = DiscoveryNodes.builder();
        for (int i = 0; i < numberOfNodes + 1; i++) {
            final DiscoveryNode node = newNode(i);
            discoBuilder = discoBuilder.put(node);
        }
        discoBuilder.localNodeId(newNode(0).id());
        discoBuilder.masterNodeId(newNode(1).id()); // we need a non-local master to test shard failures
        IndexMetaData indexMetaData = IndexMetaData.builder(index).settings(Settings.builder()
                .put(SETTING_VERSION_CREATED, Version.CURRENT)
                .put(SETTING_NUMBER_OF_SHARDS, 1).put(SETTING_NUMBER_OF_REPLICAS, 1)
                .put(SETTING_CREATION_DATE, System.currentTimeMillis())).build();
        ClusterState.Builder state = ClusterState.builder(new ClusterName("test"));
        state.nodes(discoBuilder);
        state.metaData(MetaData.builder().put(indexMetaData, false).generateClusterUuidIfNeeded());
        IndexRoutingTable.Builder indexRoutingTableBuilder = IndexRoutingTable.builder(indexMetaData.getIndex());
        for (int i = 0; i < numberOfShards; i++) {
            RoutingTable.Builder routing = new RoutingTable.Builder();
            routing.addAsNew(indexMetaData);
            final ShardId shardId = new ShardId(index, "_na_", i);
            IndexShardRoutingTable.Builder indexShardRoutingBuilder = new IndexShardRoutingTable.Builder(shardId);
            indexShardRoutingBuilder.addShard(TestShardRouting.newShardRouting(index, i, newNode(0).id(), null, null, true, ShardRoutingState.STARTED, null));
            indexShardRoutingBuilder.addShard(TestShardRouting.newShardRouting(index, i, newNode(1).id(), null, null, false, ShardRoutingState.STARTED, null));
            indexRoutingTableBuilder.addIndexShard(indexShardRoutingBuilder.build());
        }
        state.routingTable(RoutingTable.builder().add(indexRoutingTableBuilder.build()).build());
        return state.build();
    }

    /**
     * Creates cluster state with and index that has one shard and as many replicas as numberOfReplicas.
     * Primary will be STARTED in cluster state but replicas will be one of UNASSIGNED, INITIALIZING, STARTED or RELOCATING.
     *
     * @param index              name of the index
     * @param activePrimaryLocal if active primary should coincide with the local node in the cluster state
     * @param numberOfReplicas   number of replicas
     */
    public static ClusterState stateWithActivePrimary(String index, boolean activePrimaryLocal, int numberOfReplicas) {
        int assignedReplicas = randomIntBetween(0, numberOfReplicas);
        return stateWithActivePrimary(index, activePrimaryLocal, assignedReplicas, numberOfReplicas - assignedReplicas);
    }

    /**
     * Creates cluster state with and index that has one shard and as many replicas as numberOfReplicas.
     * Primary will be STARTED in cluster state. Some (unassignedReplicas) will be UNASSIGNED and
     * some (assignedReplicas) will be one of INITIALIZING, STARTED or RELOCATING.
     *
     * @param index              name of the index
     * @param activePrimaryLocal if active primary should coincide with the local node in the cluster state
     * @param assignedReplicas   number of replicas that should have INITIALIZING, STARTED or RELOCATING state
     * @param unassignedReplicas number of replicas that should be unassigned
     */
    public static ClusterState stateWithActivePrimary(String index, boolean activePrimaryLocal, int assignedReplicas, int unassignedReplicas) {
        ShardRoutingState[] replicaStates = new ShardRoutingState[assignedReplicas + unassignedReplicas];
        // no point in randomizing - node assignment later on does it too.
        for (int i = 0; i < assignedReplicas; i++) {
            replicaStates[i] = randomFrom(ShardRoutingState.INITIALIZING, ShardRoutingState.STARTED, ShardRoutingState.RELOCATING);
        }
        for (int i = assignedReplicas; i < replicaStates.length; i++) {
            replicaStates[i] = ShardRoutingState.UNASSIGNED;
        }
        return state(index, activePrimaryLocal, randomFrom(ShardRoutingState.STARTED, ShardRoutingState.RELOCATING), replicaStates);
    }

    /**
     * Creates a cluster state with no index
     */
    public static ClusterState stateWithNoShard() {
        int numberOfNodes = 2;
        DiscoveryNodes.Builder discoBuilder = DiscoveryNodes.builder();
        Set<String> unassignedNodes = new HashSet<>();
        for (int i = 0; i < numberOfNodes + 1; i++) {
            final DiscoveryNode node = newNode(i);
            discoBuilder = discoBuilder.put(node);
            unassignedNodes.add(node.id());
        }
        discoBuilder.localNodeId(newNode(0).id());
        discoBuilder.masterNodeId(newNode(1).id());
        ClusterState.Builder state = ClusterState.builder(new ClusterName("test"));
        state.nodes(discoBuilder);
        state.metaData(MetaData.builder().generateClusterUuidIfNeeded());
        state.routingTable(RoutingTable.builder().build());
        return state.build();
    }

    /**
     * Creates a cluster state where local node and master node can be specified
     * @param localNode  node in allNodes that is the local node
     * @param masterNode node in allNodes that is the master node. Can be null if no master exists
     * @param allNodes   all nodes in the cluster
     * @return cluster state
     */
    public static  ClusterState state(DiscoveryNode localNode, DiscoveryNode masterNode, DiscoveryNode... allNodes) {
        DiscoveryNodes.Builder discoBuilder = DiscoveryNodes.builder();
        for (DiscoveryNode node : allNodes) {
            discoBuilder.put(node);
        }
        if (masterNode != null) {
            discoBuilder.masterNodeId(masterNode.id());
        }
        discoBuilder.localNodeId(localNode.id());

        ClusterState.Builder state = ClusterState.builder(new ClusterName("test"));
        state.nodes(discoBuilder);
        state.metaData(MetaData.builder().generateClusterUuidIfNeeded());
        return state.build();
    }

    private static DiscoveryNode newNode(int nodeId) {
        return new DiscoveryNode("node_" + nodeId, DummyTransportAddress.INSTANCE, Version.CURRENT);
    }

    static private String selectAndRemove(Set<String> strings) {
        String selection = randomFrom(strings.toArray(new String[strings.size()]));
        strings.remove(selection);
        return selection;
    }
}
